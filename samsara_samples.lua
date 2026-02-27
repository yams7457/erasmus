-- samsara_samples
-- sample playback (MxSamples engine)
-- + samsara-style live looper (softcut)
--
-- Grid 128 layout:
--   Row 1, cols 1-5:   Beat length binary bits (16,8,4,2,1)
--   Row 1, cols 6-10:  (dark/unused)
--   Row 1, col 11:     Buffer mute (momentary, kills playback + recording)
--   Row 1, col 12:     Preserve snap to 0% (momentary)
--   Row 1, col 13:     Preserve -5%
--   Row 1, col 14:     Preserve +5%
--   Row 1, col 15:     Preserve snap 98%
--   Row 1, col 16:     Preserve snap 100%
--   Row 2, cols 1-8:   (dark/unused)
--   Row 2, col 9:      Shuffle by 1 beat
--   Row 2, col 10:     Tap tempo (blinks on beat)
--   Row 2, col 11:     Toggle hold/oneshot for last played pad
--   Row 2, col 12:     Shuffle by 1/2 beat
--   Row 2, col 14:     Listen + record (momentary)
--   Row 2, col 15:     Listen only (momentary)
--   Row 2, col 16:     Shuffle by 1/4 beat (finest)
--   Rows 3-8, cols 1-13: Sample pads
--   Row 3, col 14:     Isolator: Kill lows (<250 Hz) (momentary)
--   Row 3, col 15:     Isolator: Kill mids (250-3.5k Hz) (momentary)
--   Row 3, col 16:     Isolator: Kill highs (>3.5k Hz) (momentary)
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
local SAMPLE_DIR = _path.audio .. "samsara_samples/"
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
local preserve_value = 1.0         -- continuous 0.0-1.0
local current_playing_pad = nil    -- which sample pad index is currently active

-- Per-sample state, indexed by sample index
local pad_modes = {}  -- "oneshot" or "hold"
local pad_amps = {}   -- playback boost per pad (E3 adjustable, 0.25–4.0, default 2.0)

-- Momentary button state
local buffer_mute_held = false     -- row 1 col 11: mute buffer playback + recording
local preserve0_held = false       -- row 1 col 12: snap preserve to 0
local saved_preserve_value = nil   -- saved value while preserve0 held
local listen_rec_held = false      -- {14,2} listen + record
local listen_only_held = false     -- {15,2} listen only

-- Tap tempo
local tap_times = {}
local TAP_TIMEOUT = 2.0
local TAP_MIN_TAPS = 2
local TAP_MAX_TAPS = 6

-- Beat flash
local beat_flash_time = 0

-- Shuffle flash
local shuffle1_flash_time = 0
local shuffle2_flash_time = 0
local shuffle4_flash_time = 0

-- Preserve increment/decrement flash
local preserve_inc_flash_time = 0
local preserve_dec_flash_time = 0

-- Isolator state (momentary kill, cols 14-16, rows 3-8; one active at a time)
local iso_held = nil  -- {col=, row=} of held button, or nil

-- ─── Helpers ───

-- Map sample index (1-based) to grid position {col, row}
local function sample_to_grid(idx)
  if not samples[idx] then return nil, nil end
  return samples[idx].grid_col, samples[idx].grid_row
end

-- Map grid position to sample index (1-based), or nil if not a sample pad
local function grid_to_sample(col, row)
  if row < 3 or row > 8 then return nil end
  if col < 1 or col > 13 then return nil end
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

-- Find the most square-like rectangle W×H where W*H >= n
-- Prefers wider-than-tall when tied (shorter height saves vertical space)
local function best_rect(n, max_w, max_h)
  if n <= 0 then return 0, 0 end
  local bw, bh, bd = nil, nil, math.huge
  for h = 1, max_h do
    local w = math.ceil(n / h)
    if w <= max_w then
      local d = math.abs(w - h)
      if d < bd then
        bw, bh, bd = w, h, d
      end
    end
  end
  return bw or 1, bh or 1
end

-- Assign per-group brightness: same evenly-spaced values as before (4 to 12),
-- but randomly shuffled so adjacent groups get visually distinct brightnesses.
-- With N groups and N distinct values, every group gets a unique brightness.
local function compute_group_brightness(num_groups)
  group_brightness = {}
  if num_groups <= 1 then
    group_brightness[1] = 8
    return
  end

  -- One brightness per group, evenly spaced from 4 to 12 (same set as before)
  local values = {}
  for i = 1, num_groups do
    values[i] = 4 + math.floor((i - 1) * 8 / (num_groups - 1))
  end

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

  -- Check if assignment has any adjacency conflicts
  local function has_conflict(vals)
    for g = 1, num_groups do
      for neighbor, _ in pairs(adj[g]) do
        if vals[g] == vals[neighbor] then return true end
      end
    end
    return false
  end

  -- Shuffle (Fisher-Yates). With all distinct values (<=9 groups), the first
  -- shuffle always satisfies adjacency. With duplicates (10+ groups), retry.
  for _ = 1, 100 do
    for i = num_groups, 2, -1 do
      local j = math.random(i)
      values[i], values[j] = values[j], values[i]
    end
    if not has_conflict(values) then break end
  end

  for g = 1, num_groups do
    group_brightness[g] = values[g]
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
    print("samsara_samples: could not scan " .. SAMPLE_DIR)
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

  -- Shelf-packing layout into grid rows 3-8, cols 1-13 (14-16 reserved for isolator)
  local cursor_col = 1
  local cursor_row = 3
  local shelf_height = 0
  local max_row = 8

  for g_idx = 1, #groups do
    local group = groups[g_idx]
    local file_count = math.min(#group.files, MAX_SAMPLES - num_samples)
    if file_count <= 0 then break end

    local rows_remaining = max_row - cursor_row + 1
    local w, h = best_rect(file_count, 13, rows_remaining)

    -- Check if group fits horizontally; if not, start a new shelf
    if cursor_col + w - 1 > 13 then
      cursor_row = cursor_row + shelf_height
      cursor_col = 1
      shelf_height = 0
      rows_remaining = max_row - cursor_row + 1
      w, h = best_rect(file_count, 13, rows_remaining)
    end

    -- Check if group fits vertically
    if cursor_row + h - 1 > max_row then break end

    -- Place samples left-to-right, top-to-bottom within the rectangle
    local file_idx = 1
    for r = cursor_row, cursor_row + h - 1 do
      if not grid_samples[r] then grid_samples[r] = {} end
      for c = cursor_col, cursor_col + w - 1 do
        if file_idx > #group.files or num_samples >= MAX_SAMPLES then break end
        local filepath = group.files[file_idx]
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
        grid_samples[r][c] = num_samples
        file_idx = file_idx + 1
      end
    end

    group_names[g_idx] = group.name
    shelf_height = math.max(shelf_height, h)

    print("samsara_samples: group " .. g_idx .. " [" .. group.name .. "] " ..
      (file_idx - 1) .. " samples (" .. w .. "x" .. h .. " at col " ..
      cursor_col .. ", row " .. cursor_row .. ")")

    cursor_col = cursor_col + w  -- no gap; brightness distinguishes groups
  end

  -- Compute per-group brightness (needs grid layout to detect adjacency)
  compute_group_brightness(#groups)

  print("samsara_samples: " .. num_samples .. " total samples in " ..
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
    print("samsara_samples: all samples loaded")
    grid_dirty = true
    is_screen_dirty = true
  end)
end

-- ─── Sample Triggering ───
local function trigger_sample(idx)
  if idx < 1 or idx > num_samples then return end
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

  -- ── Row 1, col 11: Buffer mute (momentary) ──
  if row == 1 and col == 11 then
    if z == 1 then
      buffer_mute_held = true
      looper:set_buffer_muted(true)
    else
      buffer_mute_held = false
      looper:set_buffer_muted(false)
    end
    grid_dirty = true
    is_screen_dirty = true
    return
  end

  -- ── Row 1, cols 12-16: Preserve controls ──
  if row == 1 and col >= 12 and col <= 16 then
    if col == 12 then
      -- Snap to 0% (momentary)
      if z == 1 then
        preserve0_held = true
        saved_preserve_value = preserve_value
        preserve_value = 0
        looper:set_pre_level(0)
      else
        preserve0_held = false
        if saved_preserve_value then
          preserve_value = saved_preserve_value
          looper:set_pre_level(preserve_value)
          saved_preserve_value = nil
        end
      end
    elseif not preserve0_held and z == 1 then
      -- Ignore cols 13-16 while preserve0 is held
      if col == 13 then
        -- -5%
        preserve_value = util.clamp(preserve_value - 0.05, 0, 1)
        looper:set_pre_level(preserve_value)
        preserve_dec_flash_time = util.time()
      elseif col == 14 then
        -- +5%
        preserve_value = util.clamp(preserve_value + 0.05, 0, 1)
        looper:set_pre_level(preserve_value)
        preserve_inc_flash_time = util.time()
      elseif col == 15 then
        -- Snap 98%
        preserve_value = 0.98
        looper:set_pre_level(preserve_value)
      elseif col == 16 then
        -- Snap 100%
        preserve_value = 1.0
        looper:set_pre_level(preserve_value)
      end
    end
    grid_dirty = true
    is_screen_dirty = true
    return
  end

  -- ── Row 1, cols 6-11: unused (dark) ──
  if row == 1 then return end

  -- ── Row 2: function buttons (cols 9-16 only, cols 1-8 dark) ──
  if row == 2 then
    if col == 9 then
      if z == 1 then
        looper:beat_shuffle(1)
        shuffle1_flash_time = util.time()
        grid_dirty = true
      end
    elseif col == 10 then
      -- Tap tempo (on press only)
      if z == 1 then
        handle_tap_tempo()
      end
    elseif col == 11 then
      -- Toggle hold/oneshot for last played pad (on press only)
      if z == 1 and current_playing_pad then
        if pad_modes[current_playing_pad] == "oneshot" then
          pad_modes[current_playing_pad] = "hold"
        else
          pad_modes[current_playing_pad] = "oneshot"
        end
        grid_dirty = true
        is_screen_dirty = true
      end
    elseif col == 12 then
      if z == 1 then
        looper:beat_shuffle(0.5)
        shuffle2_flash_time = util.time()
        grid_dirty = true
      end
    elseif col == 14 then
      -- Listen + record (momentary): ADC->DAC + ADC->softcut
      if z == 1 then
        listen_rec_held = true
        audio.level_monitor(1.0)
        audio.level_adc_cut(1.0)
      else
        listen_rec_held = false
        audio.level_adc_cut(0)
        if not listen_only_held then
          audio.level_monitor(0)
        end
      end
      grid_dirty = true
    elseif col == 15 then
      -- Listen only (momentary): ADC->DAC only
      if z == 1 then
        listen_only_held = true
        audio.level_monitor(1.0)
      else
        listen_only_held = false
        if not listen_rec_held then
          audio.level_monitor(0)
        end
      end
      grid_dirty = true
    elseif col == 16 then
      if z == 1 then
        looper:beat_shuffle(0.25)
        shuffle4_flash_time = util.time()
        grid_dirty = true
      end
    end
    return
  end

  -- ── Row 3, cols 14-16: Isolator kill buttons ──
  if row == 3 and col >= 14 and col <= 16 then
    if z == 1 then
      local band = ({[14]="low", [15]="mid", [16]="high"})[col]
      iso_held = {col=col, row=row}
      looper:set_iso_cut(band)
    else
      if iso_held and iso_held.col == col and iso_held.row == row then
        iso_held = nil
        looper:clear_iso_cut()
      end
    end
    grid_dirty = true
    return
  end

  -- ── Rows 3-8, cols 1-13: Sample pads ──
  local idx = grid_to_sample(col, row)
  if idx then
    if z == 1 then
      trigger_sample(idx)
    else
      if pad_modes[idx] == "hold" and current_playing_pad == idx then
        release_sample()
      end
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
  local is_shuffle1_flash = (now - shuffle1_flash_time) < 0.12
  local is_shuffle2_flash = (now - shuffle2_flash_time) < 0.12
  local is_shuffle4_flash = (now - shuffle4_flash_time) < 0.12
  local is_preserve_inc_flash = (now - preserve_inc_flash_time) < 0.12
  local is_preserve_dec_flash = (now - preserve_dec_flash_time) < 0.12

  -- Row 1, cols 1-5: Binary beat length bits
  for col = 1, 5 do
    g:led(col, 1, beat_bits[col] and LED_BRIGHT or LED_DIM)
  end

  -- Row 1, col 11: Buffer mute
  g:led(11, 1, buffer_mute_held and LED_MAX or LED_DIM)

  -- Row 1, cols 12-16: Preserve controls
  g:led(12, 1, preserve0_held and LED_MAX or LED_DIM)
  g:led(13, 1, is_preserve_dec_flash and LED_MAX or LED_DIM)
  g:led(14, 1, is_preserve_inc_flash and LED_MAX or LED_DIM)
  g:led(15, 1, (preserve_value == 0.98) and LED_BRIGHT or LED_DIM)
  g:led(16, 1, (preserve_value == 1.0) and LED_BRIGHT or LED_DIM)

  -- Row 2 function buttons (cols 1-8 dark, handled by g:all)
  -- Col 9: Shuffle by 1 beat (coarsest)
  g:led(9, 2, is_shuffle1_flash and LED_MAX or LED_BRIGHT)
  -- Col 10: Tap tempo (blinks on beat)
  g:led(10, 2, is_beat_flash and LED_MAX or LED_DIM)

  -- Col 11: Hold/oneshot toggle
  local mode_led = LED_DIM
  if current_playing_pad and pad_modes[current_playing_pad] == "hold" then
    mode_led = LED_MED
  end
  g:led(11, 2, mode_led)

  -- Col 12: Shuffle by 1/2 beat
  g:led(12, 2, is_shuffle2_flash and LED_MAX or LED_BRIGHT)

  -- Col 13: unused (dark)
  -- Col 14-15: Listen buttons
  g:led(14, 2, listen_rec_held and LED_MAX or LED_DIM)
  g:led(15, 2, listen_only_held and LED_MAX or LED_DIM)

  -- Col 16: Shuffle by 1/4 beat (finest)
  g:led(16, 2, is_shuffle4_flash and LED_MAX or LED_BRIGHT)

  -- Rows 3-8: Sample pads (per-group brightness)
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

  -- Row 3, cols 14-16: Isolator kill buttons
  local active_iso_col = iso_held and iso_held.col or nil
  for col = 14, 16 do
    g:led(col, 3, (col == active_iso_col) and LED_MAX or LED_DIM)
  end

  g:refresh()

  -- If we're in a flash window, schedule another redraw to turn it off
  if is_beat_flash or is_shuffle1_flash or is_shuffle2_flash or is_shuffle4_flash
    or is_preserve_inc_flash or is_preserve_dec_flash then
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
  screen.text("SAMSARA SAMPLES")
  local tempo = params:get("clock_tempo")
  screen.move(right_x, y)
  screen.text_right(math.floor(tempo + 0.5) .. "bpm")

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
  screen.text_right(string.format("%.1fs", dur))

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
    screen.move(right_x, y)
    screen.text_right(pad_modes[current_playing_pad])
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
    -- Preserve (continuous, 5% steps)
    preserve_value = util.clamp(preserve_value + delta * 0.05, 0, 1.0)
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
  -- 1. Initialize looper
  looper = Looper.new()
  looper:init()
  looper:set_pre_level(preserve_value)

  -- Beat callback for grid flash
  looper.on_beat_callback = function(beat)
    beat_flash_time = util.time()
    grid_dirty = true
    is_screen_dirty = true
  end

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

  -- 4. Restore saved preset (triggers param actions to sync pad_amps)
  params:default()

  -- 5. Load samples into engine buffers
  load_samples()

  -- 6. Start looper clock
  looper:start_clock()

  -- 7. Set initial beat length from binary bits
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
