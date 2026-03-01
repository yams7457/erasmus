-- erasmus
-- sample playback (MxSamples engine)
-- + live looper (softcut)
--
-- Grid 128 layout:
--   Row 1, cols 1-5:   Beat length binary bits (16,8,4,2,1)
--   Row 1, col 6:      Preserve snap to 0% (momentary hold)
--   Row 1, col 7:      Solo mode (latch toggle)
--   Row 1, col 8:      Buffer mute (latch toggle)
--   Row 1, col 9:      Clear all (momentary: buffer + preserve + solo + mute + iso)
--   Row 1, col 10:     Snap to nearest power-of-2 beats (momentary flash)
--   Row 1, col 11:     Tap tempo (momentary, blinks on beat)
--   Row 1, col 12:     Shuffle by 1/2 beat (momentary flash)
--   Row 1, col 13:     Shuffle by 1/4 beat (momentary flash)
--   Row 1, col 14:     Isolator: Kill lows (<250 Hz) (toggle)
--   Row 1, col 15:     Isolator: Kill mids (250-3.5k Hz) (toggle)
--   Row 1, col 16:     Isolator: Kill highs (>3.5k Hz) (toggle)
--   Row 2, cols 1-16:  Waveform amplitude display (press to jump playhead)
--   Row 3, cols 1-10:  Pitch shift (-12,-10,-7,-5,-2,+2,+5,+7,+10,+12 semitones)
--   Row 3, col 16:     Record arm (idle→armed→recording→idle with loop)
--   Rows 4-8, cols 1-16: Sample pads / snapshot slots
--
-- Norns controls:
--   E1: Tempo
--   E2: Preserve (continuous, 5% steps)
--   E3: Sample amp (boost quiet samples)
--   K2: Play/pause looper
--   K3: Toggle recording on/off

local Looper = include("lib/looper")

engine.name = "MxSamples"

-- ─── Constants ───
local SAMPLE_DIR = _path.audio .. "erasmus/"
local SNAPSHOT_DIR = _path.audio .. "erasmus/snapshots/"
local MAX_SAMPLES = 80
local MAX_NUM_BEATS = 32
local SCREEN_FRAMERATE = 15
local GRID_FRAMERATE = 30
local VOICE_ID = 1  -- single voice for global choke

-- LED brightness
local LED_OFF = 0
local LED_DIM = 3
local LED_MED = 7
local LED_BRIGHT = 12
local LED_MAX = 15

-- Beat length binary bits (5 bits, MSB first: 16,8,4,2,1)
local beat_bits = {false, false, true, true, true}  -- default 0b00111 = 7, +1 = 8 beats
local beat_powers = {16, 8, 4, 2, 1}

-- ─── State ───
local looper
local g = grid.connect()
local grid_dirty = true
local is_screen_dirty = true
local screen_refresh_metro
local grid_refresh_metro

-- Sample management
local samples = {}         -- {filepath, name, slot, grid_row, grid_col} indexed 1..N
local num_samples = 0
local grid_samples = {}    -- grid_samples[row][col] = sample index, for grid->sample lookup
local group_names = {}     -- group_names[group_idx] = folder name for display
local group_brightness = {} -- group_brightness[group_idx] = LED brightness for idle pads

-- Grid state
local preserve_value = 0.98        -- continuous 0.0-1.0
local current_playing_pad = nil    -- which sample pad index is currently active

-- Per-sample state, indexed by sample index
local pad_modes = {}  -- "oneshot" or "hold"
local pad_amps = {}   -- playback boost per pad (E3 adjustable, 0.25–4.0, default 2.0)

-- Momentary / latch button state
local solo_mode = false                   -- row 1 col 10: latch, play over loop without recording
local buffer_muted = false                -- row 1 col 11: latch mute buffer + preserve 0
local saved_preserve_for_mute = nil       -- saved preserve while buffer muted
local preserve0_held = false              -- row 1 col 12: snap preserve to 0
local saved_preserve_value = nil          -- saved value while preserve0 held

-- Tap tempo
local tap_times = {}
local TAP_TIMEOUT = 2.0
local TAP_MIN_TAPS = 2
local TAP_MAX_TAPS = 6

-- Beat flash
local beat_flash_time = 0

-- Shuffle flash
local shuffle2_flash_time = 0
local shuffle4_flash_time = 0

-- Clear all flash
local clear_flash_time = 0

-- Snap-to-power-of-2 flash
local snap_pow2_flash_time = 0

-- Snapshot state
local grid_snapshots = {}  -- grid_snapshots[row][col] = base filename when snapshot saved
local snapshot_flash_time = 0
local snapshot_flash_pos = nil  -- {col=, row=} of last snapshot action

-- Isolator state (toggle kills, row 1 cols 14-16)
local iso_kills = {false, false, false}  -- [1]=low (col14), [2]=mid (col15), [3]=high (col16)

-- Pitch shift state (row 3, cols 1-10)
local pitch_values = {-12, -10, -7, -5, -2, 2, 5, 7, 10, 12}
local active_pitch_shift = 0
-- Idle brightness by magnitude: ±2→4, ±5→7, ±7→9, ±10→11, ±12→13
local pitch_idle_brightness = {13, 11, 9, 7, 4, 4, 7, 9, 11, 13}

-- Waveform display state (row 2)
local waveform_brightness = {}
local last_render_time = 0
local RENDER_INTERVAL = 0.25

-- Record arm state machine (row 3, col 16)
local rec_state = "idle"  -- "idle", "armed", "recording"

-- Preserve boost: snap to 100% while finger drumming, restore after one
-- full uninterrupted loop pass with no triggers.
local preserve_boosted = false
local trigger_this_loop = false

local function effective_pre_level()
  return preserve_boosted and 1.0 or preserve_value
end

-- ─── Helpers ───

-- Map sample index (1-based) to grid position {col, row}
local function sample_to_grid(idx)
  if not samples[idx] then return nil, nil end
  return samples[idx].grid_col, samples[idx].grid_row
end

-- Map grid position to sample index (1-based), or nil if not a sample pad
local function grid_to_sample(col, row)
  if row < 4 or row > 8 then return nil end
  if col < 1 or col > 16 then return nil end
  if not grid_samples[row] then return nil end
  return grid_samples[row][col]
end

-- Get display name from filepath
local function display_name(filepath)
  local name = filepath:match("([^/]+)$") or filepath
  name = name:match("(.+)%..+$") or name
  return name
end

-- Truncate string for screen display
local function truncate(str, max_len)
  if #str > max_len then
    return str:sub(1, max_len - 1) .. "…"
  end
  return str
end

-- Assign per-group brightness via greedy graph coloring.
-- Builds adjacency from the grid layout, then processes groups
-- most-constrained-first, picking the brightness in [4,13] that
-- maximizes the minimum difference from all assigned neighbors.
-- The group adjacency graph is always planar (2D grid packing),
-- so by the four-color theorem ≤4 distinct levels are needed.
-- With range [4,13] and min_diff=3 that gives {4,7,10,13} — always solvable.
local function compute_group_brightness(num_groups)
  group_brightness = {}
  if num_groups <= 1 then
    group_brightness[1] = 8
    return
  end

  local MIN_BRIGHT = 4
  local MAX_BRIGHT = 13

  -- Build group adjacency from grid positions (4-connected)
  local adj = {}
  for g = 1, num_groups do adj[g] = {} end
  local offsets = {{0, 1}, {0, -1}, {1, 0}, {-1, 0}}
  for idx = 1, num_samples do
    local s = samples[idx]
    local g1 = s.group_idx
    for _, off in ipairs(offsets) do
      local nr, nc = s.grid_row + off[1], s.grid_col + off[2]
      if grid_samples[nr] and grid_samples[nr][nc] then
        local g2 = samples[grid_samples[nr][nc]].group_idx
        if g1 ~= g2 then
          adj[g1][g2] = true
          adj[g2][g1] = true
        end
      end
    end
  end

  -- Process groups most-constrained-first (most neighbors)
  local order = {}
  for g = 1, num_groups do order[g] = g end
  table.sort(order, function(a, b)
    local ca, cb = 0, 0
    for _ in pairs(adj[a]) do ca = ca + 1 end
    for _ in pairs(adj[b]) do cb = cb + 1 end
    return ca > cb
  end)

  local mid = math.floor((MIN_BRIGHT + MAX_BRIGHT) / 2)

  for _, g in ipairs(order) do
    -- Collect assigned neighbor brightnesses
    local neighbor_vals = {}
    for nb, _ in pairs(adj[g]) do
      if group_brightness[nb] then
        table.insert(neighbor_vals, group_brightness[nb])
      end
    end

    if #neighbor_vals == 0 then
      group_brightness[g] = mid
    else
      -- Pick value that maximizes min distance to assigned neighbors;
      -- ties broken by proximity to range midpoint (visual balance)
      local best_val = mid
      local best_min_dist = -1
      for v = MIN_BRIGHT, MAX_BRIGHT do
        local min_dist = math.huge
        for _, nv in ipairs(neighbor_vals) do
          min_dist = math.min(min_dist, math.abs(v - nv))
        end
        if min_dist > best_min_dist
          or (min_dist == best_min_dist and math.abs(v - mid) < math.abs(best_val - mid)) then
          best_min_dist = min_dist
          best_val = v
        end
      end
      group_brightness[g] = best_val
    end
  end
end

-- ─── Sample Loading ───

local AUDIO_EXTENSIONS = {wav=true, flac=true, aif=true, aiff=true}

-- Check if a filename is an audio file
local function is_audio_file(name)
  local ext = name:match("%.([^%.]+)$")
  return ext and AUDIO_EXTENSIONS[ext:lower()]
end

-- Collect audio files from a directory using util.scandir (norns native)
local function collect_audio_files(dir_path)
  local files = {}
  local entries = util.scandir(dir_path)
  if not entries then return files end
  for _, entry in ipairs(entries) do
    -- Skip directories (util.scandir appends / to dirs)
    if not entry:match("/$") and is_audio_file(entry) then
      table.insert(files, dir_path .. entry)
    end
  end
  table.sort(files)
  return files
end

local function scan_samples()
  samples = {}
  num_samples = 0
  pad_modes = {}
  pad_amps = {}
  grid_samples = {}
  group_names = {}

  -- Ensure directory exists
  os.execute("mkdir -p " .. SAMPLE_DIR)

  -- Build ordered list of groups: {name, files}
  local groups = {}

  -- Scan root directory
  local entries = util.scandir(SAMPLE_DIR)
  if not entries then
    print("erasmus: could not scan " .. SAMPLE_DIR)
    return
  end

  -- Separate loose files and subdirectories
  local root_files = {}
  local subdirs = {}
  for _, entry in ipairs(entries) do
    if entry:match("/$") then
      table.insert(subdirs, entry)
    elseif is_audio_file(entry) then
      table.insert(root_files, SAMPLE_DIR .. entry)
    end
  end

  -- Root loose files first
  table.sort(root_files)
  if #root_files > 0 then
    table.insert(groups, {name = "(root)", files = root_files})
  end

  -- Then subdirectories, sorted alphabetically
  table.sort(subdirs)
  for _, subdir in ipairs(subdirs) do
    local dir_name = subdir:match("^(.-)/$") or subdir
    local dir_files = collect_audio_files(SAMPLE_DIR .. subdir)
    if #dir_files > 0 then
      table.insert(groups, {name = dir_name, files = dir_files})
    end
  end

  -- Flood-fill layout into grid rows 4-8, cols 1-16
  local MIN_ROW, MAX_ROW = 4, 8
  local MIN_COL, MAX_COL = 1, 16

  -- Occupied tracking table
  local occupied = {}
  for r = MIN_ROW, MAX_ROW do
    occupied[r] = {}
    for c = MIN_COL, MAX_COL do
      occupied[r][c] = false
    end
  end

  -- Find first empty cell scanning left-to-right, top-to-bottom
  local function find_first_empty()
    for r = MIN_ROW, MAX_ROW do
      for c = MIN_COL, MAX_COL do
        if not occupied[r][c] then return r, c end
      end
    end
    return nil, nil
  end

  -- Priority-queue BFS flood-fill: returns `count` cells in row-major order.
  -- Priority = Chebyshev distance from seed (expands in concentric square
  -- rings for compact shapes), tie-broken by row-major for determinism.
  local function flood_fill(seed_row, seed_col, count)
    local cells = {}
    local frontier = {{seed_row, seed_col}}
    local in_frontier = {}
    in_frontier[seed_row * 100 + seed_col] = true

    while #cells < count and #frontier > 0 do
      local cell = table.remove(frontier, 1)
      local r, c = cell[1], cell[2]
      in_frontier[r * 100 + c] = nil

      if not occupied[r][c] then
        table.insert(cells, {r, c})
        occupied[r][c] = true

        -- Add 4-connected empty neighbors to frontier
        local neighbors = {{r-1, c}, {r+1, c}, {r, c-1}, {r, c+1}}
        for _, nb in ipairs(neighbors) do
          local nr, nc = nb[1], nb[2]
          if nr >= MIN_ROW and nr <= MAX_ROW and nc >= MIN_COL and nc <= MAX_COL
            and not occupied[nr][nc] and not in_frontier[nr * 100 + nc] then
            -- Chebyshev distance → square rings; row-major tiebreak
            local dist = math.max(math.abs(nr - seed_row), math.abs(nc - seed_col))
            local key_new = dist * 10000 + nr * 100 + nc
            local inserted = false
            for i = 1, #frontier do
              local fi = frontier[i]
              local dist_i = math.max(math.abs(fi[1] - seed_row), math.abs(fi[2] - seed_col))
              local key_i = dist_i * 10000 + fi[1] * 100 + fi[2]
              if key_new < key_i then
                table.insert(frontier, i, {nr, nc})
                inserted = true
                break
              end
            end
            if not inserted then
              table.insert(frontier, {nr, nc})
            end
            in_frontier[nr * 100 + nc] = true
          end
        end
      end
    end

    -- Sort placed cells row-major so alphabetical sample order reads L→R, T→B
    table.sort(cells, function(a, b)
      if a[1] ~= b[1] then return a[1] < b[1] end
      return a[2] < b[2]
    end)

    return cells
  end

  for g_idx = 1, #groups do
    local group = groups[g_idx]
    local file_count = math.min(#group.files, MAX_SAMPLES - num_samples)
    if file_count <= 0 then break end

    local seed_r, seed_c = find_first_empty()
    if not seed_r then break end

    local cells = flood_fill(seed_r, seed_c, file_count)

    for fi = 1, #cells do
      if fi > #group.files or num_samples >= MAX_SAMPLES then break end
      local r, c = cells[fi][1], cells[fi][2]
      local filepath = group.files[fi]
      num_samples = num_samples + 1
      samples[num_samples] = {
        filepath = filepath,
        name = display_name(filepath),
        slot = num_samples - 1,
        grid_row = r,
        grid_col = c,
        group_idx = g_idx,
      }
      pad_modes[num_samples] = "hold"
      pad_amps[num_samples] = 2.0
      if not grid_samples[r] then grid_samples[r] = {} end
      grid_samples[r][c] = num_samples
    end

    group_names[g_idx] = group.name

    print("erasmus: group " .. g_idx .. " [" .. group.name .. "] " ..
      #cells .. " samples (flood-fill from row " .. seed_r .. ", col " .. seed_c .. ")")
  end

  -- Compute per-group brightness (needs grid layout to detect adjacency)
  compute_group_brightness(#groups)

  print("erasmus: " .. num_samples .. " total samples in " ..
    #groups .. " groups")
end

-- Add per-sample amplitude params (saved in presets)
-- IDs are index-based; stable as long as sample folder contents don't change.
local function add_sample_params()
  if num_samples == 0 then return end
  params:add_group("sample_levels", "Sample Levels", num_samples)
  for i = 1, num_samples do
    params:add_control(
      "sample_" .. i .. "_amp",
      samples[i].name,
      controlspec.new(0.25, 4.0, 'lin', 0.01, 2.0, "x")
    )
    params:set_action("sample_" .. i .. "_amp", function(value)
      pad_amps[i] = value
      is_screen_dirty = true
    end)
  end
end

local function load_samples()
  clock.run(function()
    for i = 1, num_samples do
      engine.mxsamplesload(samples[i].slot, samples[i].filepath)
      print("  loading [" .. i .. "/" .. num_samples .. "] " .. samples[i].name)
      if i % 10 == 0 then
        clock.sleep(0.5)
      end
    end
    clock.sleep(1.0)
    print("erasmus: all samples loaded")
    grid_dirty = true
    is_screen_dirty = true
  end)
end

-- ─── Binary Beat Bits (UI helper, no looper interaction) ───
local function set_beat_bits(num_beats)
  local val = num_beats - 1
  for i = 1, 5 do
    beat_bits[i] = val >= beat_powers[i]
    if beat_bits[i] then val = val - beat_powers[i] end
  end
end

-- ─── Buffer Snapshots ───
local snapshot_dir_ready = false

local function ensure_snapshot_dir()
  if not snapshot_dir_ready then
    os.execute("mkdir -p '" .. SNAPSHOT_DIR .. "'")
    snapshot_dir_ready = true
  end
end

local function save_snapshot(col, row)
  ensure_snapshot_dir()
  local dur = looper:get_buffer_dur()
  local bpm = params:get("clock_tempo")
  local beats = looper:get_num_beats()
  local base = string.format("snapshot_r%d_c%d_bpm%g_beats%d", row, col, bpm, beats)
  local path_l = SNAPSHOT_DIR .. base .. "_L.wav"
  local path_r = SNAPSHOT_DIR .. base .. "_R.wav"
  print("erasmus: saving snapshot to " .. path_l .. " (" .. string.format("%.2fs", dur) .. ")")
  softcut.buffer_write_mono(path_l, 0, dur, 1)
  softcut.buffer_write_mono(path_r, 0, dur, 2)
  if not grid_snapshots[row] then grid_snapshots[row] = {} end
  grid_snapshots[row][col] = base
  snapshot_flash_time = util.time()
  snapshot_flash_pos = {col = col, row = row}
  grid_dirty = true
  is_screen_dirty = true
end

local function load_snapshot(col, row)
  local base = grid_snapshots[row][col]

  -- Parse BPM and beats from snapshot filename
  local snap_bpm, snap_beats = base:match("bpm([%d%.]+)_beats(%d+)")
  snap_bpm = tonumber(snap_bpm)
  snap_beats = tonumber(snap_beats)

  if snap_bpm and snap_beats then
    -- Restore looper state: sets buffer_dur = loop_dur, rate = 1.0, playhead to 0
    looper:load_state(snap_bpm, snap_beats)
    -- Sync system clock (param action calls set_tempo which keeps rate at 1.0)
    params:set("clock_tempo", snap_bpm)
    -- Update grid UI beat bits
    set_beat_bits(snap_beats)
  end

  local dur = looper:get_buffer_dur()
  local path_l = SNAPSHOT_DIR .. base .. "_L.wav"
  local path_r = SNAPSHOT_DIR .. base .. "_R.wav"
  print("erasmus: loading snapshot from " .. path_l .. " (" .. string.format("%.2fs", dur) .. ")")
  softcut.buffer_read_mono(path_l, 0, 0, dur, 1, 0)
  softcut.buffer_read_mono(path_r, 0, 0, dur, 2, 0)
  snapshot_flash_time = util.time()
  snapshot_flash_pos = {col = col, row = row}
  grid_dirty = true
  is_screen_dirty = true
end

-- ─── Sample Triggering ───
local function trigger_sample(idx)
  if idx < 1 or idx > num_samples then return end
  if rec_state == "armed" then
    looper:start_capture()
    rec_state = "recording"
  end
  local s = samples[idx]

  -- mxsampleson(voice_id, buf_id, rate, amp, pan, attack, decay, sustain, release, lpf, hpf, delaySend, reverbSend, sampleStart)
  local amp = pad_amps[idx] or 2.0
  engine.mxsampleson(VOICE_ID, s.slot, 1.0, amp, 0.0, 0.015, 1.0, 0.9, 0.5, 20000, 10, 0.0, 0.0, 0)
  current_playing_pad = idx
  grid_dirty = true
  is_screen_dirty = true
end

local function release_sample()
  engine.mxsamplesoff(VOICE_ID)
  -- Keep current_playing_pad set so E3 can still adjust its level
  grid_dirty = true
  is_screen_dirty = true
end

-- ─── Binary Beat Length ───
local function compute_num_beats()
  local val = 0
  for i = 1, 5 do
    if beat_bits[i] then val = val + beat_powers[i] end
  end
  looper:set_num_beats(val + 1)  -- range 1-32
  grid_dirty = true
  is_screen_dirty = true
end

local SNAP_TARGET_BPM = 90

local function snap_to_power_of_2()
  local nb = looper:get_num_beats()
  -- Already a power of 2? Nothing to do.
  if nb > 0 and (nb & (nb - 1)) == 0 then return end

  -- Find lower and upper powers of 2
  local lower = 1
  while lower * 2 < nb do lower = lower * 2 end
  local upper = lower * 2
  if upper > 32 then upper = 32 end

  -- Pick nearest; ties broken by which tempo lands closer to 90 BPM
  local target
  local dist_lo = nb - lower
  local dist_hi = upper - nb
  if dist_lo < dist_hi then
    target = lower
  elseif dist_hi < dist_lo then
    target = upper
  else
    -- Equidistant: pick whichever resulting tempo is closer to target BPM
    local current_tempo = params:get("clock_tempo")
    local tempo_lo = lower * current_tempo / nb
    local tempo_hi = upper * current_tempo / nb
    if math.abs(tempo_lo - SNAP_TARGET_BPM) <= math.abs(tempo_hi - SNAP_TARGET_BPM) then
      target = lower
    else
      target = upper
    end
  end

  -- New tempo preserves loop duration: new_tempo = target * old_tempo / old_beats
  local new_tempo = util.clamp(target * params:get("clock_tempo") / nb, 20, 300)

  -- Apply atomically: batch prevents intermediate resize/rate changes
  set_beat_bits(target)
  looper:begin_batch()
  params:set("clock_tempo", new_tempo)
  compute_num_beats()
  looper:end_batch()
end

-- ─── Record Arm Helpers ───

-- Given a captured duration, find integer beat count B (1-32) where
-- 60*B/D is in [60,119]. Prefer largest power of 2; fallback to B
-- closest to 90 BPM; last resort clamp to B=1.
local function calculate_bpm(duration)
  local valid = {}
  for b = 1, 32 do
    local bpm = 60 * b / duration
    if bpm >= 60 and bpm <= 119 then
      table.insert(valid, b)
    end
  end

  if #valid == 0 then
    return 60 / duration, 1
  end

  -- Prefer largest power of 2
  local best_pow2 = nil
  for _, b in ipairs(valid) do
    if b > 0 and (b & (b - 1)) == 0 then
      if not best_pow2 or b > best_pow2 then
        best_pow2 = b
      end
    end
  end
  if best_pow2 then
    return 60 * best_pow2 / duration, best_pow2
  end

  -- No power of 2 fits: pick B giving BPM closest to 90
  local best_b = valid[1]
  local best_dist = math.abs(60 * valid[1] / duration - 90)
  for i = 2, #valid do
    local dist = math.abs(60 * valid[i] / duration - 90)
    if dist < best_dist then
      best_dist = dist
      best_b = valid[i]
    end
  end
  return 60 * best_b / duration, best_b
end

local function stop_recording()
  local duration = looper:stop_capture()
  local bpm, beats = calculate_bpm(duration)
  looper:load_state(bpm, beats)
  params:set("clock_tempo", bpm)
  set_beat_bits(beats)
  looper:set_pre_level(effective_pre_level())
  active_pitch_shift = 0
  save_snapshot(15, 3)
  rec_state = "idle"
  grid_dirty = true
  is_screen_dirty = true
end

-- ─── Tap Tempo ───
local function handle_tap_tempo()
  local now = util.time()

  -- Reset if too long since last tap
  if #tap_times > 0 and (now - tap_times[#tap_times]) > TAP_TIMEOUT then
    tap_times = {}
  end

  table.insert(tap_times, now)
  if #tap_times > TAP_MAX_TAPS then
    table.remove(tap_times, 1)
  end

  if #tap_times >= TAP_MIN_TAPS then
    local total = tap_times[#tap_times] - tap_times[1]
    local avg = total / (#tap_times - 1)
    local bpm = 60 / avg
    bpm = util.clamp(bpm, 20, 300)
    params:set("clock_tempo", bpm)
  end
end

-- ─── Grid Key Handler ───
function grid_key(col, row, z)
  -- ── Row 1, cols 1-5: Binary beat length ──
  if row == 1 and col >= 1 and col <= 5 then
    if z == 1 then
      beat_bits[col] = not beat_bits[col]
      compute_num_beats()
    end
    return
  end

  -- ── Row 1, cols 6-16: Function buttons (all on row 1) ──
  if row == 1 and col >= 6 then
    if col == 6 then
      -- Preserve 0% (momentary hold): mute output + overwrite buffer
      if z == 1 then
        preserve0_held = true
        saved_preserve_value = preserve_value
        preserve_value = 0
        looper:set_pre_level(0)
        looper:set_output_muted(true)
      else
        preserve0_held = false
        if saved_preserve_value then
          preserve_value = saved_preserve_value
          looper:set_pre_level(effective_pre_level())
          saved_preserve_value = nil
        end
        if not buffer_muted then
          looper:set_output_muted(false)
        end
      end
    elseif col == 7 and z == 1 then
      -- Solo mode (latch toggle)
      solo_mode = not solo_mode
      looper:set_solo_mode(solo_mode)
    elseif col == 8 and z == 1 then
      -- Buffer mute (latch toggle)
      if not buffer_muted then
        buffer_muted = true
        saved_preserve_for_mute = preserve_value
        preserve_value = 0
        looper:set_pre_level(0)
        looper:set_buffer_muted(true)
      else
        buffer_muted = false
        if saved_preserve_for_mute then
          preserve_value = saved_preserve_for_mute
          looper:set_pre_level(effective_pre_level())
          saved_preserve_for_mute = nil
        end
        looper:set_buffer_muted(false)
      end
    elseif col == 9 and z == 1 then
      -- Clear all: buffer + preserve + solo + mute + iso + boost
      looper:clear_buffer()
      preserve_value = 0.98
      preserve_boosted = false
      trigger_this_loop = false
      looper:set_pre_level(preserve_value)
      solo_mode = false
      looper:set_solo_mode(false)
      buffer_muted = false
      saved_preserve_for_mute = nil
      looper:set_buffer_muted(false)
      iso_kills = {false, false, false}
      looper:update_iso(false, false, false)
      clear_flash_time = util.time()
    elseif col == 10 and z == 1 then
      -- Snap to nearest power-of-2 beats
      snap_to_power_of_2()
      snap_pow2_flash_time = util.time()
    elseif col == 11 and z == 1 then
      -- Tap tempo
      handle_tap_tempo()
    elseif col == 12 and z == 1 then
      -- Shuffle by 1/2 beat
      looper:beat_shuffle(0.5)
      shuffle2_flash_time = util.time()
    elseif col == 13 and z == 1 then
      -- Shuffle by 1/4 beat
      looper:beat_shuffle(0.25)
      shuffle4_flash_time = util.time()
    elseif col >= 14 and col <= 16 and z == 1 then
      -- Isolator kill toggles (14=low, 15=mid, 16=high)
      local idx = col - 13
      iso_kills[idx] = not iso_kills[idx]
      looper:update_iso(iso_kills[1], iso_kills[2], iso_kills[3])
    end
    grid_dirty = true
    is_screen_dirty = true
    return
  end

  -- ── Row 2: Waveform display / jump-to-position ──
  if row == 2 and z == 1 then
    if rec_state == "armed" then
      looper:start_capture()
      rec_state = "recording"
    end
    local fraction = (col - 1) / 16
    looper:jump_to_position(fraction)
    -- Boost preserve to 100% while jumping around the buffer
    trigger_this_loop = true
    if not preserve_boosted and not preserve0_held and not buffer_muted then
      preserve_boosted = true
      looper:set_pre_level(1.0)
    end
    grid_dirty = true
    return
  end

  -- ── Row 3, cols 1-10: Pitch shift (cumulative) ──
  if row == 3 and col >= 1 and col <= 10 and z == 1 then
    active_pitch_shift = active_pitch_shift + pitch_values[col]
    looper:set_pitch_shift(active_pitch_shift)
    grid_dirty = true
    is_screen_dirty = true
    return
  end

  -- ── Row 3, col 16: Record arm ──
  if row == 3 and col == 16 and z == 1 then
    if rec_state == "idle" then
      rec_state = "armed"
    elseif rec_state == "armed" then
      rec_state = "idle"
    elseif rec_state == "recording" then
      stop_recording()
    end
    grid_dirty = true
    is_screen_dirty = true
    return
  end

  -- ── Rows 4-8, cols 1-16: Sample pads + snapshots ──
  local idx = grid_to_sample(col, row)
  print(string.format("grid_key: col=%d row=%d z=%d idx=%s", col, row, z, tostring(idx)))
  if idx then
    if z == 1 then
      trigger_sample(idx)
    else
      if pad_modes[idx] == "hold" and current_playing_pad == idx then
        release_sample()
      end
    end
  elseif row >= 1 and row <= 8 and col >= 1 and col <= 16 and z == 1 then
    -- Empty pad: snapshot save/load
    print(string.format("snapshot: col=%d row=%d has_existing=%s",
      col, row, tostring(grid_snapshots[row] and grid_snapshots[row][col] or false)))
    if grid_snapshots[row] and grid_snapshots[row][col] then
      load_snapshot(col, row)
    else
      save_snapshot(col, row)
    end
  end
end

-- ─── Grid LED Redraw ───
function grid_redraw()
  if not grid_dirty then return end
  grid_dirty = false

  g:all(LED_OFF)
  local now = util.time()
  local is_beat_flash = (now - beat_flash_time) < 0.08
  local is_shuffle2_flash = (now - shuffle2_flash_time) < 0.12
  local is_shuffle4_flash = (now - shuffle4_flash_time) < 0.12
  local is_snap_pow2_flash = (now - snap_pow2_flash_time) < 0.12
  local is_clear_flash = (now - clear_flash_time) < 0.12
  local is_snapshot_flash = (now - snapshot_flash_time) < 0.15

  -- Row 1, cols 1-5: Binary beat length bits
  for col = 1, 5 do
    g:led(col, 1, beat_bits[col] and LED_BRIGHT or LED_OFF)
  end

  -- Row 1, col 6: Preserve snap to 0% (momentary)
  g:led(6, 1, preserve0_held and LED_MAX or LED_DIM)
  -- Row 1, col 7: Solo mode
  g:led(7, 1, solo_mode and LED_MAX or LED_DIM)
  -- Row 1, col 8: Buffer mute
  g:led(8, 1, buffer_muted and LED_MAX or LED_DIM)
  -- Row 1, col 9: Clear all (extra dim — destructive action)
  g:led(9, 1, is_clear_flash and LED_MAX or 1)
  -- Row 1, col 10: Snap to power-of-2 beats
  g:led(10, 1, is_snap_pow2_flash and LED_MAX or LED_DIM)
  -- Row 1, col 11: Tap tempo (blinks on beat)
  g:led(11, 1, is_beat_flash and LED_MAX or LED_DIM)
  -- Row 1, col 12: Shuffle 1/2 beat
  g:led(12, 1, is_shuffle2_flash and LED_MAX or LED_MED)
  -- Row 1, col 13: Shuffle 1/4 beat
  g:led(13, 1, is_shuffle4_flash and LED_MAX or LED_MED)
  -- Row 1, cols 14-16: Isolator kills
  for col = 14, 16 do
    g:led(col, 1, iso_kills[col - 13] and LED_MAX or LED_DIM)
  end

  -- Row 2: Waveform amplitude display + playhead ticker
  local playhead_col = 0
  if looper.buffer_dur > 0 then
    playhead_col = math.floor(looper.playhead_pos / looper.buffer_dur * 16) + 1
    if playhead_col > 16 then playhead_col = 16 end
  end
  for col = 1, 16 do
    if col == playhead_col then
      g:led(col, 2, LED_MAX)
    else
      g:led(col, 2, waveform_brightness[col] or 0)
    end
  end

  -- Row 3: Pitch shift buttons (cols 1-10)
  for col = 1, 10 do
    g:led(col, 3, pitch_idle_brightness[col])
  end

  -- Row 3, col 16: Record arm LED
  if rec_state == "armed" then
    -- Blink at ~4Hz
    local phase = now % 0.25
    g:led(16, 3, phase < 0.125 and LED_MAX or LED_OFF)
  elseif rec_state == "recording" then
    g:led(16, 3, LED_MAX)
  else
    g:led(16, 3, LED_DIM)
  end

  -- Rate-limited waveform render request (~4 Hz)
  local now_render = util.time()
  if now_render - last_render_time >= RENDER_INTERVAL then
    last_render_time = now_render
    looper:request_waveform()
  end

  -- Rows 4-8: Sample pads (per-group brightness) + snapshots
  for i = 1, num_samples do
    local col, row = sample_to_grid(i)
    local level
    if current_playing_pad == i then
      level = LED_MAX
    else
      level = group_brightness[samples[i].group_idx] or LED_DIM
    end
    g:led(col, row, level)
  end

  -- Snapshot pads: show saved snapshots on empty grid positions
  for row = 1, 8 do
    if grid_snapshots[row] then
      for col = 1, 16 do
        if grid_snapshots[row][col] and not grid_to_sample(col, row) then
          local level = LED_DIM
          if is_snapshot_flash and snapshot_flash_pos
            and snapshot_flash_pos.col == col and snapshot_flash_pos.row == row then
            level = LED_MAX
          end
          g:led(col, row, level)
        end
      end
    end
  end

  g:refresh()

  -- Keep redrawing while playing (playhead ticker needs continuous updates)
  if looper:get_playing() == 1 then
    grid_dirty = true
  elseif rec_state == "armed"
    or is_beat_flash or is_shuffle2_flash or is_shuffle4_flash
    or is_snap_pow2_flash or is_clear_flash
    or is_snapshot_flash then
    grid_dirty = true
  end
end

-- ─── Screen Redraw ───
function redraw()
  screen.clear()

  local left_x = 2
  local right_x = 126
  local y = 10

  -- Header
  screen.level(15)
  screen.move(left_x, y)
  screen.text("ERASUMS")
  local tempo = params:get("clock_tempo")
  screen.move(right_x, y)
  if active_pitch_shift ~= 0 then
    local eff = looper:get_effective_tempo()
    screen.text_right(math.floor(eff + 0.5) .. "bpm (" .. math.floor(tempo + 0.5) .. ")")
  else
    screen.text_right(math.floor(tempo + 0.5) .. "bpm")
  end

  -- Loop info
  y = y + 12
  screen.level(12)
  screen.move(left_x, y)
  local nb = looper:get_num_beats()
  local bits_str = ""
  for i = 1, 5 do bits_str = bits_str .. (beat_bits[i] and "1" or "0") end
  screen.text("loop: " .. nb .. " beats [" .. bits_str .. "]")
  screen.move(right_x, y)
  local dur = looper:get_loop_dur()
  local rate = looper:get_effective_rate()
  if math.abs(rate - 1.0) > 0.005 then
    local semitones = 12 * math.log(rate) / math.log(2)
    screen.text_right(string.format("%.1fs %+.0fst", dur, semitones))
  else
    screen.text_right(string.format("%.1fs", dur))
  end

  -- Preserve
  y = y + 12
  screen.move(left_x, y)
  if preserve0_held then
    screen.text("preserve: 0% (held)")
  else
    screen.text("preserve: " .. math.floor(preserve_value * 100 + 0.5) .. "%")
  end
  screen.move(right_x, y)
  if looper.rec_level > 0 then
    if current_playing_pad then
      local amp = pad_amps[current_playing_pad] or 2.0
      screen.text_right(string.format("amp %.0f%%", amp * 100))
    else
      screen.text_right("rec ON")
    end
  else
    screen.text_right("rec OFF")
  end

  -- Sample name / mode
  y = y + 12
  screen.move(left_x, y)
  if current_playing_pad and samples[current_playing_pad] then
    screen.text(truncate(samples[current_playing_pad].name, 20))
  end

  -- Beat position bar
  y = y + 12
  screen.level(8)
  local bar_w = 90
  local bar_x = left_x
  local beat = looper:get_cur_beat()
  local fill_w = (nb > 0) and math.floor(bar_w * (beat + 1) / nb) or 0
  screen.rect(bar_x, y - 5, fill_w, 5)
  screen.fill()
  screen.level(4)
  screen.rect(bar_x, y - 5, bar_w, 5)
  screen.stroke()
  screen.level(12)
  screen.move(right_x, y)
  screen.text_right("beat " .. (beat + 1) .. "/" .. nb)

  screen.update()
end

function screen_frame_tick()
  if is_screen_dirty then
    is_screen_dirty = false
    redraw()
  end
end

-- ─── Encoder / Key Interaction ───
function enc(n, delta)
  if n == 1 then
    -- Tempo
    params:delta("clock_tempo", delta)
  elseif n == 2 then
    -- Preserve (continuous, 5% steps) — manual change cancels boost
    preserve_value = util.clamp(preserve_value + delta * 0.05, 0, 1.0)
    preserve_boosted = false
    looper:set_pre_level(preserve_value)
    grid_dirty = true
    is_screen_dirty = true
  elseif n == 3 then
    -- Per-pad amp boost (adjusts last played pad, saved in presets)
    if current_playing_pad then
      local cur = params:get("sample_" .. current_playing_pad .. "_amp")
      params:set("sample_" .. current_playing_pad .. "_amp", cur + delta * 0.25)
    end
  end
end

function key(n, z)
  if n == 2 and z == 1 then
    -- Play/pause looper
    if looper:get_playing() == 1 then
      looper:set_playing(0)
    else
      looper:set_playing(1)
    end
    grid_dirty = true
    is_screen_dirty = true
  elseif n == 3 and z == 1 then
    -- Toggle recording
    if looper.rec_level > 0 then
      looper:set_rec_level(0)
    else
      looper:set_rec_level(1.0)
    end
    is_screen_dirty = true
  end
end

-- ─── Clock callbacks ───
function clock.transport.start()
  looper:set_playing(1)
  grid_dirty = true
  is_screen_dirty = true
end

function clock.transport.stop()
  looper:set_playing(0)
  grid_dirty = true
  is_screen_dirty = true
end

-- ─── Init ───
function init()
  -- 0. Ensure snapshot directory exists
  ensure_snapshot_dir()

  -- 1. Create looper object (no softcut setup yet)
  looper = Looper.new()

  -- 2. Scan sample folder and register params
  scan_samples()
  add_sample_params()

  -- 3. Set up tempo param action
  local default_tempo_action = params:lookup_param("clock_tempo").action
  params:set_action("clock_tempo", function(value)
    if default_tempo_action then default_tempo_action(value) end
    looper:set_tempo(value)
    is_screen_dirty = true
  end)

  -- 4. Restore saved preset (triggers param actions to sync pad_amps + tempo)
  params:default()

  -- 5. Initialize looper AFTER params:default() so audio routing sticks
  --    (params:default resets cut_input_eng etc. to system defaults)
  looper:init()
  looper:set_pre_level(preserve_value)

  -- Waveform render callback: copy brightness data and mark grid dirty
  looper.on_waveform_callback = function()
    for i = 1, 16 do
      waveform_brightness[i] = looper.waveform_brightness[i] or 0
    end
    grid_dirty = true
  end

  -- Initial waveform render request
  looper:request_waveform()

  -- Beat callback for grid flash + preserve boost release
  looper.on_beat_callback = function(beat)
    beat_flash_time = util.time()
    -- On loop wrap: release preserve boost if no triggers this pass
    if beat == 0 and preserve_boosted then
      if not trigger_this_loop then
        preserve_boosted = false
        if not preserve0_held and not buffer_muted then
          looper:set_pre_level(preserve_value)
        end
      end
      trigger_this_loop = false
    end
    grid_dirty = true
    is_screen_dirty = true
  end

  -- 6. Load samples into engine buffers
  load_samples()

  -- 7. Start looper clock
  looper:start_clock()

  -- 8. Set initial beat length from binary bits
  compute_num_beats()

  -- 8. Start UI metros
  screen_refresh_metro = metro.init()
  if screen_refresh_metro then
    screen_refresh_metro.event = screen_frame_tick
    screen_refresh_metro:start(1 / SCREEN_FRAMERATE)
  end

  grid_refresh_metro = metro.init()
  if grid_refresh_metro then
    grid_refresh_metro.event = grid_redraw
    grid_refresh_metro:start(1 / GRID_FRAMERATE)
  end

  -- 9. Connect grid
  g.key = grid_key
  grid.add = function(dev)
    g = grid.connect()
    g.key = grid_key
    grid_dirty = true
  end

  is_screen_dirty = true
  grid_dirty = true
end

-- ─── Cleanup ───
function cleanup()
  params:write()

  -- Stop playback
  engine.mxsamplesoff(VOICE_ID)
  engine.mxsamplesrelease()

  -- Free metros
  if screen_refresh_metro then
    metro.free(screen_refresh_metro.id)
    screen_refresh_metro = nil
  end
  if grid_refresh_metro then
    metro.free(grid_refresh_metro.id)
    grid_refresh_metro = nil
  end

  -- Cleanup looper (restores audio levels, cancels clock)
  if looper then
    looper:cleanup()
  end
end
