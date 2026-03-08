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
--   K1: Norns system menu
--   K2: Play/pause all loopers
--   K3: (unmapped — rec arm is on grid col 15)

local Looper    = include("lib/looper")
local state     = include("lib/state")
local Snapshots = include("lib/snapshots")
local Samples   = include("lib/samples")
local Recording = include("lib/recording")
local ScreenUI  = include("lib/screen_ui")
local GridUI    = include("lib/grid_ui")
local AudioIO   = include("lib/audio_io")

engine.name = "MxSamplesErasmus"

-- ─── Constants ───
local SCREEN_FRAMERATE = 15
local GRID_FRAMERATE = 30
local ENG_LEVEL = 1.0

-- Local state (not shared)
local screen_refresh_metro
local grid_refresh_metro

-- Connect grid device
state.g = grid.connect()

-- Initialize modules with shared state
Snapshots.init(state)
Samples.init(state, Snapshots)
Recording.init(state, Snapshots)
ScreenUI.init(state, Looper)
AudioIO.init(state)

-- Global engine->softcut bus
local function refresh_global_eng_cut()
  audio.level_eng_cut(ENG_LEVEL)
end

-- ─── Encoder / Key Interaction ───
function enc(n, delta)
  if n == 1 then
    params:delta("clock_tempo", delta)
  elseif n == 2 then
    local tgts = state.target_tracks()
    for _, ti in ipairs(tgts) do
      state.track_preserve[ti] = util.clamp(state.track_preserve[ti] + delta * 0.05, 0, 1.0)
      state.track_preserve_boosted[ti] = false
      state.tracks[ti]:set_pre_level(state.track_preserve[ti])
    end
    state.grid_dirty = true
    state.is_screen_dirty = true
  elseif n == 3 then
    if state.current_playing_pad then
      local cur = params:get("sample_" .. state.current_playing_pad .. "_amp")
      params:set("sample_" .. state.current_playing_pad .. "_amp", cur + delta * 0.25)
    end
  end
end

function key(n, z)
  if n == 2 and z == 1 then
    local new_state = state.tracks[1]:get_playing() == 1 and 0 or 1
    for i = 1, 3 do
      state.tracks[i]:set_playing(new_state)
    end
    state.grid_dirty = true
    state.is_screen_dirty = true
  end
  -- K1: norns system menu; K3: unmapped (rec arm is on grid col 15)
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
  Snapshots.scan()
  Samples.scan()
  Samples.add_params()

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

  -- 5. Initialize softcut — reset once, then init all 3 loopers
  softcut.reset()

  audio.level_eng(ENG_LEVEL)
  refresh_global_eng_cut()
  audio.level_adc(0)
  audio.level_adc_cut(0)
  audio.level_tape_cut(0)
  audio.level_cut(1)

  softcut.buffer_clear()

  for i = 1, 3 do
    state.tracks[i]:init()
    state.tracks[i]:set_pre_level(state.track_preserve[i])
  end

  state.refresh_input_routing()

  -- Phase polling dispatch
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
    if state.reset_counter_beats > 0 then
      state.global_beat_count = state.global_beat_count + 1
      if state.global_beat_count % state.reset_counter_beats == 0 then
        for i = 1, 3 do state.tracks[i]:jump_to_mark() end
      end
    end

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
  for i = 1, 3 do
    local track_idx = i
    state.tracks[i].on_sub_tick = function(sub)
      if state.track_preserve0_held[track_idx] then
        state.tracks[track_idx]:clear_name_data_at(sub)
        return
      end
      if state.track_writing_name[track_idx] then
        state.tracks[track_idx]:set_name_at(sub, state.track_writing_name[track_idx])
      end
    end
  end

  -- 6. Load samples into engine buffers
  Samples.load_into_engine()

  -- 7. Start clocks for all tracks
  for i = 1, 3 do
    state.tracks[i]:start_clock()
    state.tracks[i]:start_iso_clock()
  end

  -- 8. Initialize grid UI
  GridUI.init(state, {
    snapshots = Snapshots,
    samples = Samples,
    recording = Recording,
    audio_io = AudioIO,
  })

  -- 9. Start UI metros
  screen_refresh_metro = metro.init()
  if screen_refresh_metro then
    screen_refresh_metro.event = ScreenUI.frame_tick
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

  for i = 1, state.next_engine_slot do
    engine.mxsamplesoff(i)
  end
  engine.mxsamplesrelease()

  if screen_refresh_metro then
    metro.free(screen_refresh_metro.id)
    screen_refresh_metro = nil
  end
  if grid_refresh_metro then
    metro.free(grid_refresh_metro.id)
    grid_refresh_metro = nil
  end

  for i = 1, 3 do
    if state.tracks[i] then
      state.tracks[i]:cleanup()
    end
  end
end

-- Expose redraw globally for norns
function redraw()
  ScreenUI.redraw()
end
