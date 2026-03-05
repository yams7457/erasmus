-- erasmus
-- sample playback (MxSamples engine)
-- + 3 independent stereo loopers (softcut, 6 voices)
--
-- Grid 256 layout: see lib/grid_ui.lua
--
-- Norns controls:
--   E1: Tempo
--   E2: Preserve (continuous, 5% steps, applies to selected track; all tracks when global)
--   E3: Sample amp (boost quiet samples)
--   K2: Play/pause all loopers
--   K3: Record arm state machine (idle->armed->recording->idle)

local Looper = include("lib/looper")
local GridUI = include("lib/grid_ui")

engine.name = "MxSamples"

-- ─── Constants ───
local SAMPLE_DIR = _path.audio .. "erasmus/"
local SNAPSHOT_DIR = _path.audio .. "erasmus/snapshots/"
local MAX_SAMPLES = 128
local MAX_NUM_BEATS = 64
local SCREEN_FRAMERATE = 15
local GRID_FRAMERATE = 30
local ENG_LEVEL = 1 / 1.4

-- ─── Shared State ───
-- Single mutable state table shared with lib/grid_ui.lua.
-- Tables are shared by reference; scalars are read/written via state.xxx.
local state = {
  tracks = {},
  selected_track = 1,   -- 1-4 (4 = global)
  recording_target = 1, -- 1-3, which track gets engine audio
  g = nil,              -- grid device, set below
  grid_dirty = true,
  is_screen_dirty = true,

  -- Toolbar / menu
  active_menu = nil,              -- nil or toolbar col (1, 2, 3, 4, 5) with open menu
  toolbar_held = nil,             -- toolbar col being physically held
  length_hold_made_selection = false,
  shuffle_flash_time = 0,         -- flash timestamp for shuffle button

  -- Per-track state (indexed 1-3)
  track_iso_kills = {{false,false,false}, {false,false,false}, {false,false,false}},
  track_preserve = {0.98, 0.98, 0.98},
  track_preserve_boosted = {false, false, false},
  track_trigger_this_loop = {false, false, false},
  track_preserve0_held = {false, false, false},
  track_saved_preserve = {nil, nil, nil},
  track_recording_enabled = {true, true, true},
  track_output_muted = {false, false, false},    -- track mute: mutes playback output
  track_reversed = {false, false, false},        -- reverse playback per track
  track_writing_name = {nil, nil, nil},          -- active sample name being written per track

  -- Reset counter (6 bits -> beat interval; 0 = disabled)
  reset_bits = {false, false, false, false, false, false},
  reset_counter_beats = 0,
  global_beat_count = 0,

  -- Sample management
  samples = {},
  num_samples = 0,
  grid_samples = {},
  group_names = {},
  group_brightness = {},

  -- Grid state
  current_playing_pad = nil,

  -- Per-sample state
  pad_amps = {},

  -- Clear flash (per-track and global)
  clear_flash_time = {0, 0, 0},
  global_clear_flash_time = 0,

  -- Cue points (placed on sample plane, jump to stored position)
  cue_points = {},         -- list of {track_idx, fraction, grid_row, grid_col}
  grid_cue_points = {},    -- reverse lookup: grid_cue_points[row][col] = cue index

  -- Scene snapshots (all 3 tracks saved/loaded together)
  snapshots = {},          -- list of {grid_row, grid_col, base, bpm, beats={b1,b2,b3}}
  grid_snapshots = {},     -- reverse lookup: grid_snapshots[row][col] = snapshot index
  snapshot_flash_time = 0,

  -- Record arm state machine (K3)
  rec_state = "idle",  -- "idle", "armed", "recording"

  -- Tap tempo
  tap_times = {},       -- list of recent tap timestamps
  tap_tempo_max = 4,    -- number of taps to average
}

-- Local state (not shared with grid)
local screen_refresh_metro
local grid_refresh_metro

-- Connect grid device
state.g = grid.connect()

-- ─── Shared Helper Functions ───
-- Placed on state table so grid_ui.lua can call them.

function state.effective_pre_level(track_idx)
  return state.track_preserve_boosted[track_idx] and 1.0 or state.track_preserve[track_idx]
end

function state.target_tracks()
  if state.selected_track == 4 then
    return {1, 2, 3}
  else
    return {state.selected_track}
  end
end

function state.sample_to_grid(idx)
  if not state.samples[idx] then return nil, nil end
  return state.samples[idx].grid_col, state.samples[idx].grid_row
end

function state.grid_to_sample(col, row)
  if row < 3 or row > 16 then return nil end
  if col < 1 or col > 16 then return nil end
  if not state.grid_samples[row] then return nil end
  return state.grid_samples[row][col]
end

-- Grid slot numbering: row 3 col 1 = 1, row 3 col 2 = 2, ..., row 16 col 16 = 224
local function grid_slot_number(row, col)
  return (row - 3) * 16 + col
end

local function is_prime(n)
  if n < 2 then return false end
  if n <= 3 then return true end
  if n % 2 == 0 or n % 3 == 0 then return false end
  local i = 5
  while i * i <= n do
    if n % i == 0 or n % (i + 2) == 0 then return false end
    i = i + 6
  end
  return true
end

function state.is_prime_slot(row, col)
  return is_prime(grid_slot_number(row, col))
end

function state.is_slot_occupied(r, c)
  if state.grid_samples[r] and state.grid_samples[r][c] then return true end
  if state.grid_cue_points[r] and state.grid_cue_points[r][c] then return true end
  if state.grid_snapshots[r] and state.grid_snapshots[r][c] then return true end
  return false
end

function state.find_free_sample_slot()
  for r = 3, 16 do
    for c = 1, 16 do
      if not state.is_prime_slot(r, c) and not state.is_slot_occupied(r, c) then
        return r, c
      end
    end
  end
  return nil, nil
end

-- Cue points prefer prime slots (distributed across grid), then any free slot
function state.find_free_cue_slot()
  for r = 3, 16 do
    for c = 1, 16 do
      if state.is_prime_slot(r, c) and not state.is_slot_occupied(r, c) then
        return r, c
      end
    end
  end
  for r = 3, 16 do
    for c = 1, 16 do
      if not state.is_slot_occupied(r, c) then
        return r, c
      end
    end
  end
  return nil, nil
end

function state.find_free_snapshot_slot()
  for r = 3, 16 do
    for c = 1, 16 do
      if not state.is_slot_occupied(r, c) then
        return r, c
      end
    end
  end
  return nil, nil
end

-- ─── Helpers ───

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

-- Refresh engine->softcut input routing for all tracks
function state.refresh_input_routing()
  for i = 1, 3 do
    local level = 0
    if state.tracks[i].capturing then
      level = 1.0  -- force on during recording
    elseif i == state.recording_target then
      local has_iso = state.track_iso_kills[i][1] or state.track_iso_kills[i][2] or state.track_iso_kills[i][3]
      level = has_iso and 0 or 1.0
    end
    state.tracks[i]:set_engine_input(level)
  end
end

-- Global engine->softcut bus
local function refresh_global_eng_cut()
  audio.level_eng_cut(ENG_LEVEL)
end

-- ─── Snapshots ───

local snapshot_dir_ready = false

local function ensure_snapshot_dir()
  if not snapshot_dir_ready then
    os.execute("mkdir -p '" .. SNAPSHOT_DIR .. "'")
    snapshot_dir_ready = true
  end
end

function state.save_snapshot()
  ensure_snapshot_dir()
  local row, col = state.find_free_snapshot_slot()
  if not row then
    print("erasmus: no free grid slot for snapshot")
    return
  end

  local bpm = params:get("clock_tempo")
  local b1 = state.tracks[1].num_beats
  local b2 = state.tracks[2].num_beats
  local b3 = state.tracks[3].num_beats
  local base = string.format("snap_r%dc%d_bpm%g_b%d_%d_%d", row, col, bpm, b1, b2, b3)

  for ti = 1, 3 do
    local t = state.tracks[ti]
    local off = t.buffer_offset
    local dur = t.buffer_dur
    if dur > 0 then
      softcut.buffer_write_mono(SNAPSHOT_DIR .. base .. "_t" .. ti .. "_L.wav", off, dur, 1)
      softcut.buffer_write_mono(SNAPSHOT_DIR .. base .. "_t" .. ti .. "_R.wav", off, dur, 2)
    end
  end

  local snap = {grid_row = row, grid_col = col, base = base, bpm = bpm, beats = {b1, b2, b3}}
  table.insert(state.snapshots, snap)
  if not state.grid_snapshots[row] then state.grid_snapshots[row] = {} end
  state.grid_snapshots[row][col] = #state.snapshots

  state.snapshot_flash_time = util.time()
  state.grid_dirty = true
  state.is_screen_dirty = true
  print("erasmus: saved snapshot to " .. base)
end

function state.load_snapshot(row, col)
  if not state.grid_snapshots[row] or not state.grid_snapshots[row][col] then return end
  local snap_idx = state.grid_snapshots[row][col]
  local snap = state.snapshots[snap_idx]
  if not snap then return end

  -- Clear writing names before restoring
  for ti = 1, 3 do
    state.track_writing_name[ti] = nil
  end

  -- Restore state for all 3 tracks (load_state BEFORE tempo change so
  -- set_tempo computes rate = loop_dur / loop_dur = 1.0 correctly)
  for ti = 1, 3 do
    local t = state.tracks[ti]
    t:load_state(snap.bpm, snap.beats[ti])

    local path_l = SNAPSHOT_DIR .. snap.base .. "_t" .. ti .. "_L.wav"
    local path_r = SNAPSHOT_DIR .. snap.base .. "_t" .. ti .. "_R.wav"
    local off = t.buffer_offset
    local dur = t.buffer_dur
    if dur > 0 then
      softcut.buffer_read_mono(path_l, 0, off, dur, 1, 0)
      softcut.buffer_read_mono(path_r, 0, off, dur, 2, 0)
    end

    -- Reset pitch, reverse, and iso state
    t.pitch_shift_semitones = 0
    t:set_pitch_shift(0)
    state.track_reversed[ti] = false
    t:set_reversed(false)
    state.track_iso_kills[ti] = {false, false, false}
    t:update_iso(false, false, false)
  end
  params:set("clock_tempo", snap.bpm)

  state.refresh_input_routing()
  state.snapshot_flash_time = util.time()
  state.grid_dirty = true
  state.is_screen_dirty = true
  print("erasmus: loaded snapshot " .. snap.base)
end

local function scan_snapshots()
  ensure_snapshot_dir()
  state.snapshots = {}
  state.grid_snapshots = {}

  local entries = util.scandir(SNAPSHOT_DIR)
  if not entries then return end

  -- Group by base name (one base = one scene, 6 WAV files)
  local seen = {}
  for _, entry in ipairs(entries) do
    local base = entry:match("^(snap_r%d+c%d+_bpm[%d%.]+_b%d+_%d+_%d+)_t%d_[LR]%.wav$")
    if base and not seen[base] then
      seen[base] = true
      local row, col, bpm, b1, b2, b3 = base:match(
        "^snap_r(%d+)c(%d+)_bpm([%d%.]+)_b(%d+)_(%d+)_(%d+)$")
      row = tonumber(row)
      col = tonumber(col)
      bpm = tonumber(bpm)
      b1 = tonumber(b1)
      b2 = tonumber(b2)
      b3 = tonumber(b3)
      if row and col and bpm and b1 and b2 and b3 then
        local snap = {grid_row = row, grid_col = col, base = base, bpm = bpm, beats = {b1, b2, b3}}
        table.insert(state.snapshots, snap)
        if not state.grid_snapshots[row] then state.grid_snapshots[row] = {} end
        state.grid_snapshots[row][col] = #state.snapshots
        print("erasmus: found snapshot " .. base)
      end
    end
  end
end

-- Assign per-group brightness via greedy graph coloring.
local function compute_group_brightness(num_groups)
  state.group_brightness = {}
  if num_groups <= 1 then
    state.group_brightness[1] = 8
    return
  end

  local MIN_BRIGHT = 4
  local MAX_BRIGHT = 13

  local adj = {}
  for grp = 1, num_groups do adj[grp] = {} end
  local offsets = {{0, 1}, {0, -1}, {1, 0}, {-1, 0}}
  for idx = 1, state.num_samples do
    local s = state.samples[idx]
    local g1 = s.group_idx
    for _, off in ipairs(offsets) do
      local nr, nc = s.grid_row + off[1], s.grid_col + off[2]
      if state.grid_samples[nr] and state.grid_samples[nr][nc] then
        local g2 = state.samples[state.grid_samples[nr][nc]].group_idx
        if g1 ~= g2 then
          adj[g1][g2] = true
          adj[g2][g1] = true
        end
      end
    end
  end

  local order = {}
  for grp = 1, num_groups do order[grp] = grp end
  table.sort(order, function(a, b)
    local ca, cb = 0, 0
    for _ in pairs(adj[a]) do ca = ca + 1 end
    for _ in pairs(adj[b]) do cb = cb + 1 end
    return ca > cb
  end)

  local mid = math.floor((MIN_BRIGHT + MAX_BRIGHT) / 2)

  for _, grp in ipairs(order) do
    local neighbor_vals = {}
    for nb, _ in pairs(adj[grp]) do
      if state.group_brightness[nb] then
        table.insert(neighbor_vals, state.group_brightness[nb])
      end
    end

    if #neighbor_vals == 0 then
      state.group_brightness[grp] = mid
    else
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
      state.group_brightness[grp] = best_val
    end
  end
end

-- Get audio file duration in seconds
local function get_file_duration(filepath)
  local info = _norns.sound_file_inspect(filepath)
  if info and info[1] > 0 then
    return info[3] / info[1]  -- frames / sample_rate
  end
  return nil
end

-- ─── Sample Loading ───

local AUDIO_EXTENSIONS = {wav=true, flac=true, aif=true, aiff=true}

local function is_audio_file(name)
  local ext = name:match("%.([^%.]+)$")
  return ext and AUDIO_EXTENSIONS[ext:lower()]
end

-- Parse a config.txt file for per-sample overrides.
-- Format: one entry per line, "sample_name: rate=X amp=Y" (fields optional).
-- Lines starting with # are comments. Blank lines are skipped.
-- Returns table keyed by sample name (without extension).
local function parse_sample_config(dir_path)
  local config = {}
  local f = io.open(dir_path .. "config.txt", "r")
  if not f then return config end
  for line in f:lines() do
    line = line:match("^%s*(.-)%s*$")  -- trim
    if line ~= "" and not line:match("^#") then
      local name, rest = line:match("^([^:]+):%s*(.+)$")
      if name and rest then
        name = name:match("^%s*(.-)%s*$")
        local entry = {}
        for key, val in rest:gmatch("(%w+)%s*=%s*([%d%.%-]+)") do
          entry[key] = tonumber(val)
        end
        config[name] = entry
      end
    end
  end
  f:close()
  return config
end

local function collect_audio_files(dir_path)
  local files = {}
  local entries = util.scandir(dir_path)
  if not entries then return files end
  for _, entry in ipairs(entries) do
    if not entry:match("/$") and is_audio_file(entry) then
      table.insert(files, dir_path .. entry)
    end
  end
  table.sort(files)
  return files
end

local function scan_samples()
  state.samples = {}
  state.num_samples = 0
  state.pad_amps = {}
  state.grid_samples = {}
  state.group_names = {}

  os.execute("mkdir -p " .. SAMPLE_DIR)

  local groups = {}

  local entries = util.scandir(SAMPLE_DIR)
  if not entries then
    print("erasmus: could not scan " .. SAMPLE_DIR)
    return
  end

  local root_files = {}
  local subdirs = {}
  for _, entry in ipairs(entries) do
    if entry:match("/$") then
      local dir_name = entry:match("^(.-)/$") or entry
      if dir_name ~= "snapshots" then
        table.insert(subdirs, entry)
      end
    elseif is_audio_file(entry) then
      table.insert(root_files, SAMPLE_DIR .. entry)
    end
  end

  table.sort(root_files)
  if #root_files > 0 then
    local root_config = parse_sample_config(SAMPLE_DIR)
    table.insert(groups, {name = "(root)", files = root_files, config = root_config})
  end

  table.sort(subdirs)
  for _, subdir in ipairs(subdirs) do
    local dir_name = subdir:match("^(.-)/$") or subdir
    local dir_path = SAMPLE_DIR .. subdir
    local dir_files = collect_audio_files(dir_path)
    if #dir_files > 0 then
      local dir_config = parse_sample_config(dir_path)
      table.insert(groups, {name = dir_name, files = dir_files, config = dir_config})
    end
  end

  -- Flood-fill layout into grid rows 3-16, cols 1-16 (224 slots)
  local MIN_ROW, MAX_ROW = 3, 16
  local MIN_COL, MAX_COL = 1, 16

  local occupied = {}
  for r = MIN_ROW, MAX_ROW do
    occupied[r] = {}
    for c = MIN_COL, MAX_COL do
      -- Reserve prime slots for cue points, and existing snapshot slots
      local has_snap = state.grid_snapshots[r] and state.grid_snapshots[r][c]
      occupied[r][c] = state.is_prime_slot(r, c) or (has_snap ~= nil)
    end
  end

  local function find_first_empty()
    for r = MIN_ROW, MAX_ROW do
      for c = MIN_COL, MAX_COL do
        if not occupied[r][c] then return r, c end
      end
    end
    return nil, nil
  end

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

        local neighbors = {{r-1, c}, {r+1, c}, {r, c-1}, {r, c+1}}
        for _, nb in ipairs(neighbors) do
          local nr, nc = nb[1], nb[2]
          if nr >= MIN_ROW and nr <= MAX_ROW and nc >= MIN_COL and nc <= MAX_COL
            and not occupied[nr][nc] and not in_frontier[nr * 100 + nc] then
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

    table.sort(cells, function(a, b)
      if a[1] ~= b[1] then return a[1] < b[1] end
      return a[2] < b[2]
    end)

    return cells
  end

  for g_idx = 1, #groups do
    local group = groups[g_idx]
    local file_count = math.min(#group.files, MAX_SAMPLES - state.num_samples)
    if file_count <= 0 then break end

    local seed_r, seed_c = find_first_empty()
    if not seed_r then break end

    local cells = flood_fill(seed_r, seed_c, file_count)

    for fi = 1, #cells do
      if fi > #group.files or state.num_samples >= MAX_SAMPLES then break end
      local r, c = cells[fi][1], cells[fi][2]
      local filepath = group.files[fi]
      local name = display_name(filepath)
      local cfg = group.config and group.config[name] or {}
      state.num_samples = state.num_samples + 1
      state.samples[state.num_samples] = {
        filepath = filepath,
        name = name,
        slot = state.num_samples - 1,
        grid_row = r,
        grid_col = c,
        group_idx = g_idx,
        rate = cfg.rate or 1.0,
      }
      state.pad_amps[state.num_samples] = cfg.amp or 2.0
      if not state.grid_samples[r] then state.grid_samples[r] = {} end
      state.grid_samples[r][c] = state.num_samples
    end

    state.group_names[g_idx] = group.name

    print("erasmus: group " .. g_idx .. " [" .. group.name .. "] " ..
      #cells .. " samples (flood-fill from row " .. seed_r .. ", col " .. seed_c .. ")")
  end

  compute_group_brightness(#groups)

  print("erasmus: " .. state.num_samples .. " total samples in " ..
    #groups .. " groups")
end

local function add_sample_params()
  if state.num_samples == 0 then return end
  params:add_group("sample_levels", "Sample Levels", state.num_samples)
  for i = 1, state.num_samples do
    params:add_control(
      "sample_" .. i .. "_amp",
      state.samples[i].name,
      controlspec.new(0.25, 4.0, 'lin', 0.01, 2.0, "x")
    )
    params:set_action("sample_" .. i .. "_amp", function(value)
      state.pad_amps[i] = value
      state.is_screen_dirty = true
    end)
  end
end

local function load_samples()
  clock.run(function()
    for i = 1, state.num_samples do
      engine.mxsamplesload(state.samples[i].slot, state.samples[i].filepath)
      print("  loading [" .. i .. "/" .. state.num_samples .. "] " .. state.samples[i].name)
      if i % 10 == 0 then
        clock.sleep(0.5)
      end
    end
    clock.sleep(1.0)
    print("erasmus: all samples loaded")
    state.grid_dirty = true
    state.is_screen_dirty = true
  end)
end

-- ─── Record Arm Helpers ───

local SNAP_TARGET_BPM = 90

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

-- ─── Sample Triggering ───
function state.stop_sample(idx)
  if idx < 1 or idx > state.num_samples then return end
  engine.mxsamplesoff(idx)
  if state.current_playing_pad == idx then
    state.current_playing_pad = nil
  end
end

function state.trigger_sample(idx)
  if idx < 1 or idx > state.num_samples then return end
  -- If record armed, start recording on recording_target track
  if state.rec_state == "armed" and not state.tracks[state.recording_target].capturing then
    state.tracks[state.recording_target]:start_recording()
    softcut.level_input_cut(1, state.tracks[state.recording_target].voice_l, 1.0)
    softcut.level_input_cut(2, state.tracks[state.recording_target].voice_r, 1.0)
    refresh_global_eng_cut()
    state.rec_state = "recording"
  end
  local s = state.samples[idx]

  local amp = state.pad_amps[idx] or 2.0
  local rate = s.rate or 1.0
  engine.mxsampleson(idx, s.slot, rate, amp, 0.0, 0.015, 1.0, 0.9, 0.5, 20000, 10, 0.0, 0.0, 0)
  state.current_playing_pad = idx

  -- Set name for writing into name_data buffer
  local ti = state.recording_target
  state.track_writing_name[ti] = s.name

  -- Boost preserve to 100% on recording_target track while finger drumming
  state.track_trigger_this_loop[ti] = true
  if not state.track_preserve_boosted[ti] and not state.track_preserve0_held[ti] then
    state.track_preserve_boosted[ti] = true
    state.tracks[ti]:set_pre_level(1.0)
  end

  state.grid_dirty = true
  state.is_screen_dirty = true
end

local function stop_recording()
  local t = state.tracks[state.recording_target]
  local duration = t:stop_recording()
  local bpm, beats = calculate_bpm(duration)
  for j = 1, 3 do state.tracks[j].pitch_shift_semitones = 0 end
  t:load_state(bpm, beats)
  params:set("clock_tempo", bpm)
  for j = 1, 3 do state.tracks[j]:set_pitch_shift(0) end
  t:set_pre_level(state.effective_pre_level(state.recording_target))
  state.track_iso_kills[state.recording_target] = {false, false, false}
  t:update_iso(false, false, false)
  state.refresh_input_routing()
  refresh_global_eng_cut()
  state.rec_state = "idle"
  state.grid_dirty = true
  state.is_screen_dirty = true
end

-- ─── Screen Redraw (3-column scrolling name display) ───

-- Column layout
local COL_X = {1, 44, 87}
local COL_W = 42
local NAME_MAX_CHARS = 7
local ROW_H = 8
local HEADER_H = 8
local NUM_ROWS = 7       -- rows visible per column (3 past + center + 3 future)
local CENTER_ROW = 4     -- which row is the "now" row (1-indexed)
local GAP_TOLERANCE = 4  -- subs of nil between same name counts as continuous

-- Per-track brightness: center row (playhead) and dim (surrounding)
local COL_BRIGHT = {15, 9, 5}
local COL_DIM = {8, 5, 3}

-- Collect deduplicated name entries around current sub for a track.
-- Returns {past={}, future={}} where each entry is {name=, offset=}.
-- past is ordered nearest-first, future is ordered nearest-first.
local function collect_names(track, subs_per_beat)
  local total = track:name_total_subs()
  if total == 0 then return {past = {}, future = {}} end

  local cur = track.iso_sub % total
  local half = math.floor(total / 2)

  -- Scan outward, collect name changes (deduplicate consecutive runs)
  local past = {}   -- offset < 0
  local future = {} -- offset >= 0

  -- Scan forward (future): from cur to cur + half
  local last_name = nil
  local gap = 0
  for off = 0, half do
    local sub = (cur + off) % total
    local name = track.name_data[sub]
    if name then
      if name ~= last_name or gap > GAP_TOLERANCE then
        table.insert(future, {name = name, offset = off})
        last_name = name
      end
      gap = 0
    else
      gap = gap + 1
    end
  end

  -- Scan backward (past): from cur-1 to cur - half
  last_name = nil
  gap = 0
  -- We collect in reverse order, then the list ends up nearest-first
  for off = 1, half do
    local sub = (cur - off) % total
    local name = track.name_data[sub]
    if name then
      if name ~= last_name or gap > GAP_TOLERANCE then
        table.insert(past, {name = name, offset = -off})
        last_name = name
      end
      gap = 0
    else
      gap = gap + 1
    end
  end

  return {past = past, future = future}
end

function redraw()
  screen.clear()
  screen.font_size(8)

  -- Header row
  local tempo = params:get("clock_tempo")
  screen.level(15)
  screen.move(1, HEADER_H)
  screen.text(math.floor(tempo + 0.5) .. "bpm")

  -- Rec state on right
  screen.move(126, HEADER_H)
  if state.rec_state == "armed" then
    screen.text_right("ARM")
  elseif state.rec_state == "recording" then
    screen.text_right("REC")
  end

  -- 3 columns
  local subs_per_beat = Looper.ISO_SUBS_PER_BEAT
  for ti = 1, 3 do
    local t = state.tracks[ti]
    local names = collect_names(t, subs_per_beat)
    local x = COL_X[ti]
    local bright = COL_BRIGHT[ti]
    local dim = COL_DIM[ti]

    -- Build display rows: past above center, future from center down
    local rows = {}
    for r = 1, NUM_ROWS do rows[r] = nil end

    -- Center row = first future entry (current or next name)
    if #names.future > 0 then
      rows[CENTER_ROW] = names.future[1].name
    end

    -- Past rows: above center (row 3, 2, 1)
    for p = 1, math.min(#names.past, CENTER_ROW - 1) do
      rows[CENTER_ROW - p] = names.past[p].name
    end

    -- Future rows below center (row 5, 6, 7)
    for f = 2, math.min(#names.future, NUM_ROWS - CENTER_ROW + 1) do
      rows[CENTER_ROW + f - 1] = names.future[f].name
    end

    -- Draw rows
    for r = 1, NUM_ROWS do
      if rows[r] then
        local y = HEADER_H + r * ROW_H
        local display = rows[r]
        if #display > NAME_MAX_CHARS then
          display = display:sub(1, NAME_MAX_CHARS)
        end
        screen.level(r == CENTER_ROW and bright or dim)
        screen.move(x, y)
        screen.text(display)
      end
    end
  end

  screen.update()
end

local function screen_frame_tick()
  -- Always redraw while any track is playing (names scroll continuously)
  local any_playing = false
  for i = 1, 3 do
    if state.tracks[i]:get_playing() == 1 then any_playing = true; break end
  end
  if any_playing or state.is_screen_dirty then
    state.is_screen_dirty = false
    redraw()
  end
end

-- ─── Encoder / Key Interaction ───
function enc(n, delta)
  if n == 1 then
    -- Tempo
    params:delta("clock_tempo", delta)
  elseif n == 2 then
    -- Preserve (continuous, 5% steps)
    local tgts = state.target_tracks()
    for _, ti in ipairs(tgts) do
      state.track_preserve[ti] = util.clamp(state.track_preserve[ti] + delta * 0.05, 0, 1.0)
      state.track_preserve_boosted[ti] = false
      state.tracks[ti]:set_pre_level(state.track_preserve[ti])
    end
    state.grid_dirty = true
    state.is_screen_dirty = true
  elseif n == 3 then
    -- Per-pad amp boost
    if state.current_playing_pad then
      local cur = params:get("sample_" .. state.current_playing_pad .. "_amp")
      params:set("sample_" .. state.current_playing_pad .. "_amp", cur + delta * 0.25)
    end
  end
end

function key(n, z)
  if n == 2 and z == 1 then
    -- Play/pause all loopers
    local new_state = state.tracks[1]:get_playing() == 1 and 0 or 1
    for i = 1, 3 do
      state.tracks[i]:set_playing(new_state)
    end
    state.grid_dirty = true
    state.is_screen_dirty = true
  elseif n == 3 and z == 1 then
    -- Record arm state machine
    if state.rec_state == "idle" then
      state.rec_state = "armed"
    elseif state.rec_state == "armed" then
      state.rec_state = "idle"
    elseif state.rec_state == "recording" then
      stop_recording()
    end
    state.is_screen_dirty = true
  end
end

-- ─── Clock callbacks ───
function clock.transport.start()
  for i = 1, 3 do
    state.tracks[i]:set_playing(1)
  end
  state.grid_dirty = true
  state.is_screen_dirty = true
end

function clock.transport.stop()
  for i = 1, 3 do
    state.tracks[i]:set_playing(0)
  end
  state.grid_dirty = true
  state.is_screen_dirty = true
end

-- ─── Init ───
function init()
  -- 1. Create 3 Looper instances
  state.tracks[1] = Looper.new(1, 1, 2, 0)
  state.tracks[2] = Looper.new(2, 3, 4, 100)
  state.tracks[3] = Looper.new(3, 5, 6, 200)

  -- 2. Scan snapshots first (so sample flood-fill avoids their slots), then samples
  scan_snapshots()
  scan_samples()
  add_sample_params()

  -- 3. Set up tempo param action (shared across all tracks)
  local default_tempo_action = params:lookup_param("clock_tempo").action
  params:set_action("clock_tempo", function(value)
    if default_tempo_action then default_tempo_action(value) end
    for i = 1, 3 do
      state.tracks[i]:set_tempo(value)
    end
    state.is_screen_dirty = true
  end)

  -- 4. Restore saved preset
  params:default()

  -- 5. Initialize softcut -- reset once, then init all 3 loopers
  softcut.reset()

  -- Audio routing (transient only — never use params:set for system audio)
  audio.level_eng(ENG_LEVEL)
  refresh_global_eng_cut()
  audio.level_adc_cut(0)
  audio.level_tape_cut(0)
  audio.level_cut(1)

  softcut.buffer_clear()

  for i = 1, 3 do
    state.tracks[i]:init()
    state.tracks[i]:set_pre_level(state.track_preserve[i])
  end

  -- Input routing: only recording_target track receives engine input
  state.refresh_input_routing()

  -- Phase polling dispatch: route L voice of each track to its instance
  local voice_to_track = {[1]=1, [3]=2, [5]=3}
  softcut.event_phase(function(voice, pos)
    local ti = voice_to_track[voice]
    if ti then state.tracks[ti]:on_phase(pos) end
  end)
  for i = 1, 3 do
    softcut.phase_quant(state.tracks[i].voice_l, 1/30)
  end
  softcut.poll_start_phase()

  -- Beat callback: uses track 1 for shared beat clock
  state.tracks[1].on_beat_callback = function(beat)
    -- Reset counter
    if state.reset_counter_beats > 0 then
      state.global_beat_count = state.global_beat_count + 1
      if state.global_beat_count % state.reset_counter_beats == 0 then
        for i = 1, 3 do state.tracks[i]:jump_to_mark() end
      end
    end

    -- Per-track boost release on loop wrap
    for i = 1, 3 do
      if beat == 0 and state.track_preserve_boosted[i] then
        if not state.track_trigger_this_loop[i] then
          state.track_preserve_boosted[i] = false
          if not state.track_preserve0_held[i] then
            state.tracks[i]:set_pre_level(state.track_preserve[i])
          end
        end
        state.track_trigger_this_loop[i] = false
        state.track_writing_name[i] = nil
      end
    end

    -- Re-enforce engine->softcut routing
    refresh_global_eng_cut()
    state.refresh_input_routing()

    state.grid_dirty = true
    state.is_screen_dirty = true
  end

  -- Per-track iso tick callbacks
  for i = 1, 3 do
    local track_idx = i
    state.tracks[i].on_iso_tick = function(sub, kills)
      if state.track_preserve0_held[track_idx] then
        state.tracks[track_idx]:clear_iso_data_at(sub)
        return
      end
      -- Guard: if recording disabled, don't save iso and clear stored data
      if not state.track_recording_enabled[track_idx] then
        state.tracks[track_idx]:clear_iso_data_at(sub)
        return
      end
      local k = state.track_iso_kills[track_idx]
      if kills[1] ~= k[1] or kills[2] ~= k[2] or kills[3] ~= k[3] then
        state.track_iso_kills[track_idx] = {kills[1], kills[2], kills[3]}
        state.tracks[track_idx]:update_iso(kills[1], kills[2], kills[3])
        state.refresh_input_routing()
        state.grid_dirty = true
      end
    end
  end

  -- Per-track name_data sub tick callbacks
  -- Unlike iso_data (a control layer), name_data describes what audio is in the
  -- buffer. Only erase names when audio is actually being erased (preserve0 held),
  -- and only write names when new audio is actively being recorded.
  for i = 1, 3 do
    local track_idx = i
    state.tracks[i].on_sub_tick = function(sub)
      if state.track_preserve0_held[track_idx] then
        -- Audio is being erased at this position
        state.tracks[track_idx]:clear_name_data_at(sub)
        return
      end
      if state.track_writing_name[track_idx] and state.track_recording_enabled[track_idx] then
        state.tracks[track_idx]:set_name_at(sub, state.track_writing_name[track_idx])
      end
    end
  end

  -- 6. Load samples into engine buffers
  load_samples()

  -- 7. Start clocks for all tracks
  for i = 1, 3 do
    state.tracks[i]:start_clock()
    state.tracks[i]:start_iso_clock()
  end

  -- 8. Initialize grid UI
  GridUI.init(state)

  -- 9. Start UI metros
  screen_refresh_metro = metro.init()
  if screen_refresh_metro then
    screen_refresh_metro.event = screen_frame_tick
    screen_refresh_metro:start(1 / SCREEN_FRAMERATE)
  end

  grid_refresh_metro = metro.init()
  if grid_refresh_metro then
    grid_refresh_metro.event = GridUI.redraw
    grid_refresh_metro:start(1 / GRID_FRAMERATE)
  end

  -- 10. Connect grid
  state.g.key = GridUI.key
  grid.add = function(dev)
    state.g = grid.connect()
    state.g.key = GridUI.key
    state.grid_dirty = true
  end

  state.is_screen_dirty = true
  state.grid_dirty = true

end

-- ─── Cleanup ───
function cleanup()
  params:write()

  -- Stop all engine voices
  for i = 1, state.num_samples do
    engine.mxsamplesoff(i)
  end
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

  -- Cleanup all 3 loopers
  for i = 1, 3 do
    if state.tracks[i] then
      state.tracks[i]:cleanup()
    end
  end

  -- No system audio restore needed — we only use transient audio.* calls
end
