-- lib/grid_ui.lua
-- Grid key handling and LED drawing for Erasmus
-- Separated from erasmus.lua for faster interface iteration
--
-- Grid 256 layout:
--   Row 1, cols 1-16 (toolbar):
--     Menus:     Col 1: Track Select  Col 2: Length  Col 3: Pitch  Col 4: Isolator  Col 5: Shuffle
--     Gap:       Col 6: dark
--     Actions:   Col 7: Momentary Clear  Col 8: Toggle Record  Col 9: Full Clear  Col 10: Track Mute
--     Tempo:     Col 11: Tap Tempo
--     Gap:       Col 12: dark
--     Audio In:  Col 13: ADC Monitor  Col 14: ADC Record (includes monitor)
--     Record:    Col 15: Rec Arm
--     Save:      Col 16: Save Snapshot
--   Row 2: Menu area (horizontal options), or loop position tracker + jump-to-position (when no menu open)
--   Rows 3-16: Sample pads + cue points + scene snapshots (14 rows x 16 cols = 224 slots)
--   Empty sample pad tap: creates cue point at current playhead position

local GridUI = {}

-- Module-level references (set by init)
local S
local Snapshots
local Samples
local Recording
local AudioIO

-- LED brightness constants
local LED_OFF = 0
local LED_DIM = 3
local LED_MED = 7
local LED_BRIGHT = 12
local LED_MAX = 15

-- Track Select toolbar brightness: T1=15, T2=9, T3=4, G=2
local TRACK_SELECT_BRIGHTNESS = {15, 9, 4, 2}

-- Cue point per-track brightness (bright/dim for blinking)
local CUE_BRIGHT = {12, 7, 4}
local CUE_DIM = {6, 3, 2}

-- Pitch shift display
local pitch_values = {-12, -10, -7, -5, -2, 2, 5, 7, 10, 12}
-- Idle brightness by magnitude: +/-2->4, +/-5->7, +/-7->9, +/-10->11, +/-12->13
local pitch_idle_brightness = {13, 11, 9, 7, 4, 4, 7, 9, 11, 13}

-- Snapshot glow timing (matches iso clock subdivision)
local ISO_SUBS_PER_BEAT = 32

-- Beat shuffle slice counts (menu options)
local shuffle_slice_counts = {3, 4, 5, 6, 7, 8, 12}

-- Length encoding: base of 1 + additive powers [1, 2, 4, 8, 16, 32]
-- All off = 1 beat. Each button adds its power. Max = 1+63 = 64.
local length_add_values = {1, 2, 4, 8, 16, 32}

local function get_length_bits(val)
  -- Subtract base of 1, then extract which additive powers are active
  local remainder = val - 1
  local bits = {}
  for i = 6, 1, -1 do
    if remainder >= length_add_values[i] then
      bits[i] = true
      remainder = remainder - length_add_values[i]
    else
      bits[i] = false
    end
  end
  return bits
end

local function bits_to_value(bits)
  local val = 1  -- base
  for i = 1, 6 do
    if bits[i] then val = val + length_add_values[i] end
  end
  return val
end

local function compute_reset_counter()
  local val = 0
  for i = 1, 6 do
    if S.reset_bits[i] then val = val + length_add_values[i] end
  end
  S.reset_counter_beats = val
  S.global_beat_count = 0
end

-- Menu option counts: how many horizontal options each menu has on row 2
local MENU_COLS = {
  [1] = {count = 4},   -- Track Select
  [2] = {count = 6},   -- Length
  [3] = {count = 12},  -- Pitch (10 intervals + gap + reverse)
  [4] = {count = 4},   -- Iso (3 bands + clear)
  [5] = {count = 7},   -- Beat Shuffle
}

-- Tap tempo: max interval before resetting tap sequence
local TAP_TIMEOUT = 2.0

-- ─── Toolbar Actions ───

local function do_tap_tempo()
  local now = util.time()
  if #S.tap_times > 0 and (now - S.tap_times[#S.tap_times]) > TAP_TIMEOUT then
    S.tap_times = {}
  end
  table.insert(S.tap_times, now)
  while #S.tap_times > S.tap_tempo_max do
    table.remove(S.tap_times, 1)
  end
  if #S.tap_times >= 2 then
    local total = S.tap_times[#S.tap_times] - S.tap_times[1]
    local avg_interval = total / (#S.tap_times - 1)
    if avg_interval > 0 then
      params:set("clock_tempo", 60 / avg_interval)
    end
  end
end

local function do_momentary_clear(z)
  local tgts = S.target_tracks()
  if z == 1 then
    for _, i in ipairs(tgts) do
      S.track_preserve0_held[i] = true
      S.track_saved_preserve[i] = S.track_preserve[i]
      S.track_preserve[i] = 0
      S.tracks[i]:set_pre_level(0)
      S.tracks[i]:set_output_muted(true)
    end
  else
    for _, i in ipairs(tgts) do
      S.track_preserve0_held[i] = false
      if S.track_saved_preserve[i] then
        S.track_preserve[i] = S.track_saved_preserve[i]
        S.tracks[i]:set_pre_level(S.effective_pre_level(i))
        S.track_saved_preserve[i] = nil
      end
      S.tracks[i]:set_output_muted(false)
    end
  end
end

local function do_full_clear()
  local tgts = S.target_tracks()
  for _, i in ipairs(tgts) do
    S.tracks[i]:clear_buffer()
    S.tracks[i]:clear_iso_data()
    S.tracks[i]:clear_name_data()
    S.track_iso_kills[i] = {false, false, false}
    S.tracks[i]:update_iso(false, false, false)
    S.clear_flash_time[i] = util.time()
  end
  if S.selected_track == 4 then
    S.global_clear_flash_time = util.time()
  end
  -- Remove cue points for cleared tracks
  local cleared = {}
  for _, i in ipairs(tgts) do cleared[i] = true end
  local new_cues = {}
  for _, cue in ipairs(S.cue_points) do
    if cleared[cue.track_idx] then
      if S.grid_cue_points[cue.grid_row] then
        S.grid_cue_points[cue.grid_row][cue.grid_col] = nil
      end
    else
      table.insert(new_cues, cue)
    end
  end
  S.cue_points = new_cues
  -- Rebuild grid_cue_points indices
  for idx, cue in ipairs(S.cue_points) do
    if not S.grid_cue_points[cue.grid_row] then S.grid_cue_points[cue.grid_row] = {} end
    S.grid_cue_points[cue.grid_row][cue.grid_col] = idx
  end
  S.refresh_input_routing()
end

local function do_cue_point_at(row, col)
  -- No-op when global is selected or slot is occupied
  if S.selected_track == 4 then return end
  if S.is_slot_occupied(row, col) then return end

  local track_idx = S.selected_track
  local t = S.tracks[track_idx]

  -- Compute fraction from playhead position
  local fraction = 0
  if t.buffer_dur > 0 then
    fraction = t.playhead_pos / t.buffer_dur
  end

  -- Set mark_pos for reset counter compatibility
  t:set_mark(fraction)

  -- Add cue point at the pressed pad's position
  local cue = {track_idx = track_idx, fraction = fraction, grid_row = row, grid_col = col}
  table.insert(S.cue_points, cue)
  if not S.grid_cue_points[row] then S.grid_cue_points[row] = {} end
  S.grid_cue_points[row][col] = #S.cue_points
end

local function do_toggle_record()
  local tgts = S.target_tracks()
  for _, i in ipairs(tgts) do
    S.track_recording_enabled[i] = not S.track_recording_enabled[i]
    if S.track_recording_enabled[i] then
      S.tracks[i]:set_rec_level(1.0)
    else
      -- Don't zero rec_level if ADC recording is active for this track
      if S.adc_to_softcut == 0 or i ~= S.recording_target then
        S.tracks[i]:set_rec_level(0)
      end
    end
  end
end

-- Find the most recent cue point on a track, return its fraction (or nil)
local function last_cue_fraction(track_idx)
  local latest = nil
  for i = #S.cue_points, 1, -1 do
    if S.cue_points[i].track_idx == track_idx then
      latest = S.cue_points[i].fraction
      break
    end
  end
  return latest
end

local function do_beat_shuffle(num_slices)
  local tgts = S.target_tracks()
  for _, i in ipairs(tgts) do
    local t = S.tracks[i]
    if t.num_beats > 0 then
      -- Find start offset from most recent cue point on this track
      local cue_frac = last_cue_fraction(i)
      if cue_frac then
        t:jump_to_position(cue_frac)
      end
      -- group_size = total beats / number of slices
      local group_size = t.num_beats / num_slices
      if group_size > 0 then
        t:beat_shuffle(group_size)
      end
    end
  end
  S.shuffle_flash_time = util.time()
end

local function do_reverse()
  local tgts = S.target_tracks()
  for _, i in ipairs(tgts) do
    S.track_reversed[i] = not S.track_reversed[i]
    S.tracks[i]:set_reversed(S.track_reversed[i])
  end
end

local function do_track_mute()
  local tgts = S.target_tracks()
  for _, i in ipairs(tgts) do
    S.track_output_muted[i] = not S.track_output_muted[i]
    S.tracks[i]:set_output_muted(S.track_output_muted[i])
  end
end

local function do_save_snapshot()
  Snapshots.save()
end

-- ─── Grid Key Handlers ───

local function handle_toolbar(col, z)
  -- Non-menu items: execute immediately, do NOT affect active_menu
  if col == 7 then
    do_momentary_clear(z)
    return
  end
  if col == 8 and z == 1 then
    do_toggle_record()
    return
  end
  if col == 9 and z == 1 then
    do_full_clear()
    return
  end
  if col == 10 and z == 1 then
    do_track_mute()
    return
  end
  if col == 11 and z == 1 then
    do_tap_tempo()
    return
  end
  if col == 13 and z == 1 then
    -- Toggle ADC monitor (hear external input)
    if S.adc_monitor > 0 then
      AudioIO.set_monitor(0)
    else
      AudioIO.set_monitor(1)
    end
    return
  end
  if col == 14 and z == 1 then
    -- Toggle ADC record (external input → softcut buffer; includes monitor)
    if S.adc_to_softcut > 0 then
      AudioIO.set_adc_to_softcut(0)
      AudioIO.set_monitor(0)
      -- Restore rec_level based on col 8 state
      local ti = S.recording_target
      if not S.track_recording_enabled[ti] then
        S.tracks[ti]:set_rec_level(0)
      end
    else
      AudioIO.set_adc_to_softcut(1)
      AudioIO.set_monitor(1)
      -- Ensure rec_level is on so ADC actually writes to buffer
      S.tracks[S.recording_target]:set_rec_level(1.0)
    end
    return
  end
  if col == 15 and z == 1 then
    Recording.toggle()
    return
  end
  if col == 16 and z == 1 then
    do_save_snapshot()
    return
  end

  -- Menu items: cols 1-5
  if MENU_COLS[col] then
    if z == 1 then
      S.toolbar_held = col
      if col == 2 then
        S.length_hold_made_selection = false
      end
      -- Toggle menu
      if S.active_menu == col then
        S.active_menu = nil
      else
        S.active_menu = col
      end
    else
      -- Release
      if col == 2 and S.toolbar_held == 2 then
        -- Length: if user toggled bits during hold, close menu on release
        if S.length_hold_made_selection then
          S.active_menu = nil
        end
      end
      S.toolbar_held = nil
    end
  end
end

local function handle_menu_press(col, row, z)
  if z ~= 1 then return end

  -- Any row 2 press starts recording if armed
  Recording.begin_if_armed()

  -- No menu open: row 2 press jumps to that fraction of the buffer
  if S.active_menu == nil then
    local fraction = (col - 1) / 16
    local tgts = S.target_tracks()
    for _, i in ipairs(tgts) do
      S.tracks[i]:jump_to_position(fraction)
    end
    return
  end

  -- Menus render horizontally on row 2, cols 1..N
  local menu = MENU_COLS[S.active_menu]
  if not menu then return end
  if col < 1 or col > menu.count then return end

  local option_idx = col  -- col 1 = option 1, col 2 = option 2, etc.

  if S.active_menu == 1 then
    -- Track select: cols 1-4
    local new_track = option_idx  -- 1-4
    if new_track >= 1 and new_track <= 3 then
      S.selected_track = new_track
      S.recording_target = new_track
      S.refresh_input_routing()
    elseif new_track == 4 then
      S.selected_track = 4
      -- recording_target stays at last 1-3 value
    end
    S.active_menu = nil  -- auto-close on selection

  elseif S.active_menu == 2 then
    -- Length: cols 1-6 (6-bit value)
    local bit_idx = option_idx
    if S.selected_track == 4 then
      -- Global: modify reset counter
      S.reset_bits[bit_idx] = not S.reset_bits[bit_idx]
      compute_reset_counter()
    else
      -- Per-track: modify num_beats via bitwise
      local t = S.tracks[S.selected_track]
      local cur_bits = get_length_bits(t.num_beats)
      cur_bits[bit_idx] = not cur_bits[bit_idx]
      t:set_num_beats(bits_to_value(cur_bits))
    end
    S.length_hold_made_selection = true

  elseif S.active_menu == 3 then
    if option_idx <= 10 then
      -- Pitch: cols 1-10 (accumulate; each press adds the interval)
      local delta = pitch_values[option_idx]
      local tgts = S.target_tracks()
      for _, i in ipairs(tgts) do
        local new_val = S.tracks[i].pitch_shift_semitones + delta
        if new_val ~= S.tracks[i].pitch_shift_semitones then
          S.tracks[i]:set_pitch_shift(new_val)
          -- set_pitch_shift clears iso data; reset the kill state to match
          S.track_iso_kills[i] = {false, false, false}
          S.tracks[i]:update_iso(false, false, false)
        end
      end
      S.refresh_input_routing()
    elseif option_idx == 12 then
      -- Reverse toggle
      do_reverse()
    end
    -- col 11 is a gap (no action)

  elseif S.active_menu == 4 then
    -- Iso: options 1-3 = band toggles, option 4 = clear iso data
    local band = option_idx
    if band == 4 then
      local tgts = S.target_tracks()
      for _, i in ipairs(tgts) do
        S.tracks[i]:clear_iso_data()
        S.track_iso_kills[i] = {false, false, false}
        S.tracks[i]:update_iso(false, false, false)
      end
      S.refresh_input_routing()
      return
    end
    local tgts = S.target_tracks()
    for _, i in ipairs(tgts) do
      S.track_iso_kills[i][band] = not S.track_iso_kills[i][band]
      local k = S.track_iso_kills[i]
      S.tracks[i]:update_iso(k[1], k[2], k[3])
      if S.track_recording_enabled[i] then
        S.tracks[i]:set_iso_at(S.tracks[i].iso_sub, k)
      end
    end
    S.refresh_input_routing()

  elseif S.active_menu == 5 then
    -- Beat Shuffle: cols 1-7
    local slice_count = shuffle_slice_counts[option_idx]
    if slice_count then
      do_beat_shuffle(slice_count)
    end
  end
end

local function handle_sample_pad(col, row, z)
  -- Release: stop sample/snapshot playback
  if z == 0 then
    if S.current_playing_snapshot and S.grid_snapshots[row] and S.grid_snapshots[row][col] then
      Snapshots.stop_playback()
    else
      local idx = S.grid_to_sample(col, row)
      if idx then Samples.stop(idx) end
    end
    return
  end

  -- Check for cue point
  if S.grid_cue_points[row] and S.grid_cue_points[row][col] then
    local cue_idx = S.grid_cue_points[row][col]
    local cue = S.cue_points[cue_idx]
    if cue then
      -- Cue points start recording when armed
      Recording.begin_if_armed()
      local t = S.tracks[cue.track_idx]
      t:jump_to_position(cue.fraction)
      S.track_trigger_this_loop[cue.track_idx] = true
      if not S.track_preserve_boosted[cue.track_idx] and not S.track_preserve0_held[cue.track_idx] then
        S.track_preserve_boosted[cue.track_idx] = true
        t:set_pre_level(1.0)
      end
      return
    end
  end

  -- Check for snapshot (mode depends on col 8 / track_recording_enabled)
  if S.grid_snapshots[row] and S.grid_snapshots[row][col] then
    local snap_idx = S.grid_snapshots[row][col]
    local any_rec_enabled = false
    for i = 1, 3 do
      if S.track_recording_enabled[i] then any_rec_enabled = true; break end
    end
    if any_rec_enabled then
      Snapshots.load(row, col)
    else
      Snapshots.trigger_as_sample(snap_idx)
    end
    return
  end

  -- Check for sample
  local idx = S.grid_to_sample(col, row)
  if idx then
    -- Samples start recording when armed
    Recording.begin_if_armed()
    Samples.trigger(idx)
    return
  end

  -- Empty pad: create cue point
  do_cue_point_at(row, col)
end

function GridUI.key(col, row, z)
  if row == 1 then
    handle_toolbar(col, z)
  elseif row == 2 then
    handle_menu_press(col, row, z)
  else -- row >= 3: sample pads, cue points, snapshots
    handle_sample_pad(col, row, z)
  end
  S.grid_dirty = true
  S.is_screen_dirty = true
end

-- ─── Grid LED Redraw ───

local function draw_toolbar(now)
  local g = S.g

  -- === Menus (cols 1-5) ===

  -- Col 1: Track Select (brightness indicates current selection)
  local ts_brightness = TRACK_SELECT_BRIGHTNESS[S.selected_track] or 2
  g:led(1, 1, S.active_menu == 1 and LED_MAX or ts_brightness)

  -- Col 2: Length
  g:led(2, 1, S.active_menu == 2 and LED_MAX or LED_DIM)

  -- Col 3: Pitch
  g:led(3, 1, S.active_menu == 3 and LED_MAX or LED_DIM)

  -- Col 4: Isolator
  local any_iso = false
  for i = 1, 3 do
    if S.track_iso_kills[i][1] or S.track_iso_kills[i][2] or S.track_iso_kills[i][3] then
      any_iso = true; break
    end
  end
  if S.active_menu == 4 then
    g:led(4, 1, LED_MAX)
  elseif any_iso then
    g:led(4, 1, LED_MED)
  else
    g:led(4, 1, LED_DIM)
  end

  -- Col 5: Beat Shuffle
  local shuffle_flash = (now - S.shuffle_flash_time) < 0.12
  if S.active_menu == 5 then
    g:led(5, 1, LED_MAX)
  elseif shuffle_flash then
    g:led(5, 1, LED_MAX)
  else
    g:led(5, 1, LED_DIM)
  end

  -- === Col 6: dark gap ===

  -- === Actions (cols 7-10) ===

  -- Col 7: Momentary Clear
  local any_held = S.track_preserve0_held[1] or S.track_preserve0_held[2] or S.track_preserve0_held[3]
  g:led(7, 1, any_held and LED_MAX or LED_DIM)

  -- Col 8: Toggle Record
  local any_rec_disabled = false
  local all_rec_disabled = true
  for i = 1, 3 do
    if not S.track_recording_enabled[i] then any_rec_disabled = true end
    if S.track_recording_enabled[i] then all_rec_disabled = false end
  end
  if all_rec_disabled then
    g:led(8, 1, LED_OFF)
  elseif any_rec_disabled then
    g:led(8, 1, LED_MED)
  else
    g:led(8, 1, LED_BRIGHT)
  end

  -- Col 9: Full Clear
  local any_clear_flash = false
  for i = 1, 3 do
    if (now - S.clear_flash_time[i]) < 0.12 then any_clear_flash = true; break end
  end
  if (now - S.global_clear_flash_time) < 0.12 then any_clear_flash = true end
  g:led(9, 1, any_clear_flash and LED_MAX or 1)

  -- Col 10: Track Mute
  local any_out_muted = false
  local all_out_muted = true
  for i = 1, 3 do
    if S.track_output_muted[i] then any_out_muted = true end
    if not S.track_output_muted[i] then all_out_muted = false end
  end
  if all_out_muted then
    g:led(10, 1, LED_OFF)
  elseif any_out_muted then
    g:led(10, 1, LED_MED)
  else
    g:led(10, 1, LED_BRIGHT)
  end

  -- === Col 11: Tap Tempo (beat-synced blink) ===
  local t1 = S.tracks[1]
  local tempo_phase = 0
  if t1.buffer_dur > 0 and t1.num_beats > 0 then
    local beat_dur = t1.buffer_dur / t1.num_beats
    if beat_dur > 0 then
      tempo_phase = (t1.playhead_pos / beat_dur) % 1.0
    end
  end
  g:led(11, 1, tempo_phase < 0.25 and LED_MAX or LED_DIM)

  -- === Col 12: dark gap ===

  -- === Col 13: ADC Monitor ===
  g:led(13, 1, S.adc_monitor > 0 and LED_BRIGHT or LED_OFF)

  -- === Col 14: ADC Record (includes monitor) ===
  g:led(14, 1, S.adc_to_softcut > 0 and LED_BRIGHT or LED_OFF)

  -- === Col 15: Rec Arm ===
  if S.rec_state == "recording" then
    -- Blink on beat while recording
    local t1 = S.tracks[1]
    local tap_phase = 0
    if t1.buffer_dur > 0 and t1.num_beats > 0 then
      local beat_dur = t1.buffer_dur / t1.num_beats
      if beat_dur > 0 then
        tap_phase = (t1.playhead_pos / beat_dur) % 1.0
      end
    end
    g:led(15, 1, tap_phase < 0.25 and LED_MAX or LED_MED)
  elseif S.rec_state == "armed" then
    g:led(15, 1, LED_BRIGHT)
  else
    g:led(15, 1, LED_DIM)
  end

  -- === Col 16: Save Snapshot ===
  local snap_flash = (now - S.snapshot_flash_time) < 0.15
  g:led(16, 1, snap_flash and LED_MAX or LED_DIM)
end

local function draw_menu_area(now)
  local g = S.g
  if S.active_menu == nil then return end

  if S.active_menu == 1 then
    -- Track select: row 2, cols 1-4
    for c = 1, 4 do
      if c == S.selected_track then
        g:led(c, 2, LED_MAX)
      else
        g:led(c, 2, TRACK_SELECT_BRIGHTNESS[c])
      end
    end

  elseif S.active_menu == 2 then
    -- Length: row 2, cols 1-6, show 6-bit value
    local bits
    if S.selected_track == 4 then
      bits = S.reset_bits
    else
      bits = get_length_bits(S.tracks[S.selected_track].num_beats)
    end
    for c = 1, 6 do
      g:led(c, 2, bits[c] and LED_BRIGHT or LED_DIM)
    end

  elseif S.active_menu == 3 then
    -- Pitch: row 2, cols 1-10, highlight active pitch
    local cur_pitch = 0
    if S.selected_track ~= 4 then
      cur_pitch = S.tracks[S.selected_track].pitch_shift_semitones
    end
    for c = 1, 10 do
      if pitch_values[c] == cur_pitch and cur_pitch ~= 0 then
        g:led(c, 2, LED_MAX)
      else
        g:led(c, 2, pitch_idle_brightness[c])
      end
    end
    -- Col 11: gap (dark)
    -- Col 12: Reverse toggle
    local any_reversed = S.track_reversed[1] or S.track_reversed[2] or S.track_reversed[3]
    local all_reversed = S.track_reversed[1] and S.track_reversed[2] and S.track_reversed[3]
    if S.selected_track ~= 4 then
      g:led(12, 2, S.track_reversed[S.selected_track] and LED_MAX or LED_DIM)
    elseif all_reversed then
      g:led(12, 2, LED_BRIGHT)
    elseif any_reversed then
      g:led(12, 2, LED_MED)
    else
      g:led(12, 2, LED_DIM)
    end

  elseif S.active_menu == 4 then
    -- Iso: row 2, cols 1-3 = band state, col 4 = clear
    if S.selected_track == 4 then
      for band = 1, 3 do
        local any = S.track_iso_kills[1][band] or S.track_iso_kills[2][band] or S.track_iso_kills[3][band]
        g:led(band, 2, any and LED_MAX or LED_DIM)
      end
    else
      local k = S.track_iso_kills[S.selected_track]
      for band = 1, 3 do
        g:led(band, 2, k[band] and LED_MAX or LED_DIM)
      end
    end
    g:led(4, 2, LED_DIM)  -- clear iso data button

  elseif S.active_menu == 5 then
    -- Beat Shuffle: row 2, cols 1-7, brightness scaled by slice count
    for c = 1, 7 do
      local count = shuffle_slice_counts[c]
      local brightness = math.floor(LED_DIM + (LED_BRIGHT - LED_DIM) * (count / 12))
      g:led(c, 2, brightness)
    end
  end
end

local function draw_sample_pads(now)
  local g = S.g
  for i = 1, S.num_samples do
    local col, srow = S.sample_to_grid(i)
    local level
    if S.current_playing_pad == i then
      level = LED_MAX
    else
      level = S.group_brightness[S.samples[i].group_idx] or LED_DIM
    end
    g:led(col, srow, level)
  end
end

local function draw_cue_points(now)
  local g = S.g
  for _, cue in ipairs(S.cue_points) do
    local t = S.tracks[cue.track_idx]
    -- Blink: 2-beat cycle derived from playhead position
    local blink_phase = 0
    if t.buffer_dur > 0 and t.num_beats > 0 then
      local beat_dur = t.buffer_dur / t.num_beats
      if beat_dur > 0 then
        blink_phase = (t.playhead_pos / (beat_dur * 2)) % 1.0
      end
    end
    -- On for first half of 2-beat cycle, dim for second half
    local bright = CUE_BRIGHT[cue.track_idx]
    local dim_level = CUE_DIM[cue.track_idx]
    local level = blink_phase < 0.5 and bright or dim_level
    g:led(cue.grid_col, cue.grid_row, level)
  end
end

local function draw_snapshots(now)
  local g = S.g
  local snap_flash = (now - S.snapshot_flash_time) < 0.15

  -- Tempo-synced triangle wave glow (slow pulsate: 4x slower than iso tick)
  local tempo = S.tracks[1].tempo or 120
  local tick_dur = 60 / (tempo * ISO_SUBS_PER_BEAT) * 4
  local tick = math.floor(now / tick_dur)
  local range = LED_BRIGHT - LED_DIM  -- 9
  local phase = tick % (range * 2)
  if phase > range then phase = range * 2 - phase end
  local glow_level = LED_DIM + phase

  for _, snap in ipairs(S.snapshots) do
    local level = snap_flash and LED_MAX or glow_level
    g:led(snap.grid_col, snap.grid_row, level)
  end
end

local function draw_loop_position(now)
  if S.active_menu ~= nil then return end
  local g = S.g
  -- Accumulate per-column max brightness (handles overlapping playheads)
  local col_level = {}
  for ti = 1, 3 do
    local t = S.tracks[ti]
    if t.buffer_dur > 0 then
      local frac = (t.playhead_pos / t.buffer_dur) % 1.0
      local c = math.floor(frac * 16) + 1
      if c > 16 then c = 16 end
      local brightness = TRACK_SELECT_BRIGHTNESS[ti]
      col_level[c] = math.max(col_level[c] or 0, brightness)
    end
  end
  for c, level in pairs(col_level) do
    g:led(c, 2, level)
  end
end

function GridUI.redraw()
  if not S.grid_dirty then return end
  S.grid_dirty = false

  local g = S.g
  g:all(LED_OFF)
  local now = util.time()

  draw_toolbar(now)
  draw_sample_pads(now)
  draw_snapshots(now)
  draw_cue_points(now)
  draw_menu_area(now)
  draw_loop_position(now)

  g:refresh()

  -- Keep redrawing while playing or menu open or cue points exist
  local any_playing = false
  for i = 1, 3 do
    if S.tracks[i]:get_playing() == 1 then any_playing = true; break end
  end
  if any_playing or S.active_menu ~= nil or #S.cue_points > 0 or #S.snapshots > 0 then
    S.grid_dirty = true
  else
    -- Check for active flashes
    local any_flash = false
    for i = 1, 3 do
      if (now - S.clear_flash_time[i]) < 0.12 then any_flash = true; break end
    end
    if (now - S.global_clear_flash_time) < 0.12 then any_flash = true end
    if (now - S.shuffle_flash_time) < 0.12 then any_flash = true end
    if (now - S.snapshot_flash_time) < 0.15 then any_flash = true end
    if any_flash then S.grid_dirty = true end
  end
end

function GridUI.init(shared_state, modules)
  S = shared_state
  Snapshots = modules.snapshots
  Samples = modules.samples
  Recording = modules.recording
  AudioIO = modules.audio_io
end

return GridUI
