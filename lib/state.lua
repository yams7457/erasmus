-- lib/state.lua
-- Shared mutable state table for Erasmus.
-- All modules receive a reference to this table.

local state = {
  tracks = {},
  selected_track = 1,   -- 1-4 (4 = global)
  recording_target = 1, -- 1-3, which track gets engine audio
  g = nil,              -- grid device, set in erasmus.lua
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
  snapshots = {},          -- list of {grid_row, grid_col, base, bpm, beats={b1,b2,b3}, engine_slots={}}
  grid_snapshots = {},     -- reverse lookup: grid_snapshots[row][col] = snapshot index
  snapshot_flash_time = 0,
  next_engine_slot = 0,    -- next available engine slot (set after sample scan)
  current_playing_snapshot = nil,  -- snapshot index currently being played via engine

  -- Record arm state machine (grid col 15)
  rec_state = "idle",  -- "idle", "armed", "recording"

  -- Tap tempo
  tap_times = {},       -- list of recent tap timestamps
  tap_tempo_max = 4,    -- number of taps to average
}

-- ─── Helper Functions ───

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

-- Refresh engine->softcut input routing for all tracks.
-- Iso cuts engine->buffer input so the filter "bakes" into recordings/snapshots.
function state.refresh_input_routing()
  for i = 1, 3 do
    local level = 0
    if i == state.recording_target then
      local has_iso = state.track_iso_kills[i][1] or state.track_iso_kills[i][2] or state.track_iso_kills[i][3]
      level = has_iso and 0 or 1.0
    end
    state.tracks[i]:set_engine_input(level)
  end
end

return state
