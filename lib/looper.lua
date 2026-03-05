-- lib/looper.lua
-- Erasmus softcut looper module — multi-instance (3 stereo tracks)
-- Adapted from samsara v1.4.3 by @21echoes
-- Each instance owns 2 softcut voices (L + R) forming a stereo delay loop.
-- Isolator uses post_filter (immediate audible kill) + pre_filter (prints to buffer).
-- While iso is active, engine→softcut is cut so unfiltered input can't contaminate
-- the buffer — only the pre_filtered feedback path writes back.
--
-- Uses softcut native looping for sample-accurate timing.
-- The clock coroutine only drives the UI beat counter.
--
-- Delay-line model: loop_start is fixed at buffer_offset, loop_end = buffer_offset + buffer_dur.
-- Changing beats/tempo just moves loop_end. pre_level is feedback,
-- rec_level is input mix. On resize, buffer content is rearranged
-- to preserve the most recently heard output. Softcut handles the rest.

local Looper = {}
Looper.__index = Looper

local MAX_NUM_BEATS = 64
local REGION_SIZE = 100          -- each track gets 100s of buffer space
local STAGING_OFFSET = 300       -- shared staging area at [300, 350]
local ISO_SUBS_PER_BEAT = 32     -- 128th note resolution for iso data buffer
-- Engine attenuation: instead of boosting softcut output (which bakes into
-- tape bounces), we attenuate the engine on both paths (monitoring + recording)
-- so that softcut playback at unity matches the engine. Tape-stable.
local ENG_LEVEL = 1 / 1.4

-- Constructor: each Looper instance owns a pair of softcut voices in a buffer region.
-- track_id: 1, 2, or 3
-- voice_l, voice_r: softcut voice numbers (1-6)
-- buffer_offset: start position in both softcut buffers (0, 100, or 200)
function Looper.new(track_id, voice_l, voice_r, buffer_offset)
  local self = setmetatable({}, Looper)
  self.track_id = track_id
  self.voice_l = voice_l
  self.voice_r = voice_r
  self.voices = {voice_l, voice_r}
  self.buffer_offset = buffer_offset
  self.region_size = REGION_SIZE
  self.playing = 1
  self.rec_level = 1.0
  self.pre_level = 1.0
  self.base = 2                  -- beat base: cycles 2→3→5
  self.multiplier = 4            -- num_beats = base * multiplier
  self.num_beats = 8             -- base * multiplier (default 2*4=8)
  self.tempo = 120
  self.loop_dur = (8 / 120) * 60 -- default
  self.loop_start_pos = 0        -- relative to buffer_offset
  self.loop_end_pos = 0          -- absolute buffer position of loop end (set in init)
  self.playhead_pos = 0          -- relative position tracked via phase polling
  self.cur_beat = 0
  self.clock_id = nil
  self.on_beat_callback = nil
  self.buffer_muted = false
  self.rate = 1.0
  self.buffer_dur = 0            -- set in init(), tracks actual buffer content length
  self._batch = false            -- true during atomic tempo+beats updates
  self.pitch_shift_semitones = 0
  self.reversed = false
  self.waveform_brightness = {}  -- 8-element brightness cache (compressed from 16)
  self.on_waveform_callback = nil
  self.capturing = false
  self.staging = false
  self.staging_dur = 0
  self.iso_data = {}             -- sparse change events: iso_data[sub] = {low, mid, high} or nil
  self.iso_sub = 0               -- current subdivision counter (0-based)
  self.iso_clock_id = nil
  self.on_iso_tick = nil         -- callback(sub, kills) fired when a stored event is reached
  self._iso_sweep_id = nil       -- clock id for in-progress fc sweep
  self._iso_cur_fc = nil         -- last target fc (for sweeping back to neutral)
  self._iso_cur_neutral = nil    -- neutral fc for current filter type
  self.mark_pos = 0.0            -- mark position as fraction of buffer_dur

  self.name_data = {}            -- sparse: name_data[sub] = "name" or nil
  self.on_sub_tick = nil         -- callback(sub) fired EVERY sub (not just on events)

  return self
end

function Looper:init()
  -- Set up voices in their buffer region
  for _, voice in ipairs(self.voices) do
    softcut.enable(voice, 1)
    softcut.buffer(voice, voice == self.voice_l and 1 or 2)
    softcut.pan(voice, voice == self.voice_l and -1.0 or 1.0)
    softcut.rate(voice, 1)
    -- Native looping for sample-accurate wrap
    softcut.loop(voice, 1)
    softcut.loop_start(voice, self.buffer_offset)
    softcut.position(voice, self.buffer_offset)
    -- Input routing: L input → left voice, R input → right voice (set by erasmus)
    softcut.level(voice, 1.0)
    softcut.pre_level(voice, self.pre_level)
    softcut.rec_level(voice, self.rec_level)
    -- Anti-click: fade_time enables softcut's dual-head crossfade at loop
    -- boundaries and position jumps. level_slew/recpre_slew handle level changes.
    softcut.fade_time(voice, 0.01)
    softcut.level_slew_time(voice, 0.01)
    softcut.recpre_slew_time(voice, 0.01)
    softcut.rec(voice, 1)
    softcut.play(voice, 1)
  end

  -- Both filters to passthrough. softcut.reset() defaults pre_filter_dry
  -- to 0.0 (blocks all feedback), so we MUST set dry=1.0 here.
  for _, voice in ipairs(self.voices) do
    softcut.post_filter_dry(voice, 1.0)
    softcut.post_filter_lp(voice, 0)
    softcut.post_filter_hp(voice, 0)
    softcut.post_filter_bp(voice, 0)
    softcut.post_filter_br(voice, 0)
    softcut.pre_filter_dry(voice, 1.0)
    softcut.pre_filter_lp(voice, 0)
    softcut.pre_filter_hp(voice, 0)
    softcut.pre_filter_bp(voice, 0)
    softcut.pre_filter_br(voice, 0)
    softcut.pre_filter_fc(voice, 12000)
    softcut.pre_filter_rq(voice, 2.0)
  end

  -- Set initial loop_end
  self.num_beats = self.base * self.multiplier
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self.buffer_dur = self.loop_dur
  self.rate = 1.0
  self:_apply_loop_end()
  self:_apply_rate()

  self:init_iso_data()
  self:init_name_data()

  print("looper[" .. self.track_id .. "]: init complete — voices " ..
    self.voice_l .. "," .. self.voice_r ..
    " offset=" .. self.buffer_offset ..
    " loop=" .. string.format("%.2fs", self.loop_dur))
end

-- Phase polling callback — called from erasmus's global phase dispatcher
function Looper:on_phase(pos)
  self.playhead_pos = pos - self.buffer_offset
end

-- Engine input routing for this track's voices
function Looper:set_engine_input(level)
  -- Route L input bus → left voice, R input bus → right voice
  softcut.level_input_cut(1, self.voice_l, level)
  softcut.level_input_cut(2, self.voice_r, level)
  -- Zero-out cross-channel to prevent crosstalk
  softcut.level_input_cut(2, self.voice_l, 0)
  softcut.level_input_cut(1, self.voice_r, 0)
end

function Looper:start_clock()
  self.cur_beat = 0
  self.clock_id = clock.run(function()
    while true do
      clock.sync(1)
      if self.playing == 1 then
        -- UI beat counter only -- softcut handles its own looping
        self.cur_beat = (self.cur_beat + 1) % self.num_beats

        if self.on_beat_callback then
          self.on_beat_callback(self.cur_beat)
        end
      end
    end
  end)
end

function Looper:set_pre_level(val)
  self.pre_level = val
  for _, voice in ipairs(self.voices) do
    softcut.pre_level(voice, val)
  end
end

function Looper:set_rec_level(val)
  self.rec_level = val
  if not self.buffer_muted then
    for _, voice in ipairs(self.voices) do
      softcut.rec_level(voice, val)
    end
  end
end

function Looper:set_tempo(bpm)
  self.tempo = bpm
  self.loop_dur = (self.num_beats / self.tempo) * 60
  if self._batch then return end
  -- Time-stretch: buffer stays, rate adjusts
  self.rate = self.buffer_dur / self.loop_dur
  self:_apply_rate()
end

function Looper:set_playing(val)
  if val == 1 then
    -- Resume
    for _, voice in ipairs(self.voices) do
      softcut.play(voice, 1)
      softcut.rec(voice, 1)
      if not self.buffer_muted then
        softcut.rec_level(voice, self.rec_level)
        softcut.level(voice, 1.0)
      else
        softcut.rec_level(voice, 0)
        softcut.level(voice, 0)
      end
    end
    self.playing = 1
  else
    -- Pause
    for _, voice in ipairs(self.voices) do
      softcut.play(voice, 0)
      softcut.rec(voice, 0)
      softcut.level(voice, 0.0)
    end
    self.playing = 0
  end
end

function Looper:set_buffer_muted(muted)
  self.buffer_muted = muted
  for _, voice in ipairs(self.voices) do
    if muted then
      softcut.rec_level(voice, 0)
      softcut.level(voice, 0)
    else
      softcut.rec_level(voice, self.rec_level)
      softcut.level(voice, 1.0)
    end
  end
end

function Looper:set_output_muted(muted)
  for _, voice in ipairs(self.voices) do
    softcut.level(voice, muted and 0 or 1.0)
  end
end

function Looper:clear_buffer()
  softcut.buffer_clear_region(self.buffer_offset, self.region_size)
end

-- ─── Beat Length Model (Base × Multiplier) ───

function Looper:set_base(new_base)
  local old_base = self.base
  self.base = new_base
  local old_beats = self.num_beats
  self.num_beats = self.base * self.multiplier
  -- Resize buffer by ratio
  local new_buffer_dur = self.buffer_dur * (new_base / old_base)
  self:_resize_buffer(new_buffer_dur)
  self:_resize_iso_data(old_beats, self.num_beats)
  self:_resize_name_data(old_beats, self.num_beats)
end

function Looper:halve_beats()
  if self.multiplier <= 1 then return end
  local old_beats = self.num_beats
  self.multiplier = self.multiplier / 2
  self.num_beats = self.base * self.multiplier
  self.loop_dur = (self.num_beats / self.tempo) * 60
  local new_buffer_dur = self.rate * self.loop_dur
  self:_resize_buffer(new_buffer_dur)
  self:_resize_iso_data(old_beats, self.num_beats)
  self:_resize_name_data(old_beats, self.num_beats)
end

function Looper:double_beats()
  local new_mult = self.multiplier * 2
  if self.base * new_mult > MAX_NUM_BEATS then return end
  local old_beats = self.num_beats
  self.multiplier = new_mult
  self.num_beats = self.base * self.multiplier
  self.loop_dur = (self.num_beats / self.tempo) * 60
  local new_buffer_dur = self.rate * self.loop_dur
  self:_resize_buffer(new_buffer_dur)
  self:_resize_iso_data(old_beats, self.num_beats)
  self:_resize_name_data(old_beats, self.num_beats)
end

function Looper:set_num_beats(val)
  val = util.clamp(math.floor(val), 1, MAX_NUM_BEATS)
  if val == self.num_beats then return end
  local old_beats = self.num_beats
  self.num_beats = val
  -- Reverse-engineer base/multiplier for backward compat
  local bases = {2, 3, 5}
  for _, b in ipairs(bases) do
    if val % b == 0 then
      self.base = b; self.multiplier = val / b; break
    end
  end
  self.loop_dur = (self.num_beats / self.tempo) * 60
  local new_buffer_dur = self.rate * self.loop_dur
  self:_resize_buffer(new_buffer_dur)
  self:_resize_iso_data(old_beats, self.num_beats)
  self:_resize_name_data(old_beats, self.num_beats)
end

-- ─── Mark Point ───

function Looper:set_mark(fraction)
  self.mark_pos = util.clamp(fraction, 0, 1.0)
end

function Looper:jump_to_mark()
  local pos = self.mark_pos * self.buffer_dur
  for _, voice in ipairs(self.voices) do
    softcut.position(voice, self.buffer_offset + pos)
  end
  -- Sync beat counter to match the new playhead position
  self.cur_beat = math.floor(self.mark_pos * self.num_beats)
end

function Looper:load_state(bpm, beats)
  self.tempo = bpm
  self.num_beats = util.clamp(beats, 1, MAX_NUM_BEATS)
  -- Reverse-engineer base/multiplier: find a valid base that divides beats
  local bases = {2, 3, 5}
  local found = false
  for _, b in ipairs(bases) do
    if beats % b == 0 then
      self.base = b
      self.multiplier = beats / b
      found = true
      break
    end
  end
  if not found then
    self.base = 2
    self.multiplier = math.ceil(beats / 2)
  end
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self.buffer_dur = self.loop_dur
  self.rate = 1.0
  self:_apply_loop_end()
  self:_apply_rate()
  for _, voice in ipairs(self.voices) do
    softcut.position(voice, self.buffer_offset)
  end
  self:init_iso_data()
  self:init_name_data()
  self.iso_sub = 0
  self.mark_pos = 0.0
end

function Looper:get_cur_beat()
  return self.cur_beat
end

function Looper:get_loop_dur()
  return self.loop_dur
end

function Looper:get_num_beats()
  return self.num_beats
end

function Looper:get_playing()
  return self.playing
end

function Looper:cleanup()
  -- Cancel clocks
  if self.clock_id then
    clock.cancel(self.clock_id)
    self.clock_id = nil
  end
  if self.iso_clock_id then
    clock.cancel(self.iso_clock_id)
    self.iso_clock_id = nil
  end
  if self._iso_sweep_id then
    clock.cancel(self._iso_sweep_id)
    self._iso_sweep_id = nil
  end
end

-- Content-preserving buffer resize.
-- On shrink: copies the most recently heard content to [offset, offset + new_buffer_dur].
-- On expand: tiles existing content to fill [offset + old_dur, offset + new_buffer_dur].
-- Blocked during capture to protect the staging area.
function Looper:_resize_buffer(new_buffer_dur)
  if self.capturing or self.staging then return end
  local old_end = self.buffer_dur
  local off = self.buffer_offset

  if new_buffer_dur < old_end and old_end > 0 then
    -- Shrinking: preserve content anchored at mark position.
    local anchor = self.mark_pos * old_end
    -- Calculate source start: center new window on mark, clamped to buffer bounds
    local src = anchor - new_buffer_dur / 2
    if src < 0 then src = 0 end
    if src + new_buffer_dur > old_end then src = old_end - new_buffer_dur end

    if src >= 0 and src + new_buffer_dur <= old_end then
      -- No wrap needed: copy from [off+src, off+src+new_dur] to staging, then back to [off, off+new_dur]
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, off + src, STAGING_OFFSET, new_buffer_dur, 0, 0)
        softcut.buffer_copy_mono(ch, ch, STAGING_OFFSET, off, new_buffer_dur, 0, 0)
      end
    else
      -- Fallback: copy from offset
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, off, STAGING_OFFSET, new_buffer_dur, 0, 0)
        softcut.buffer_copy_mono(ch, ch, STAGING_OFFSET, off, new_buffer_dur, 0, 0)
      end
    end
  elseif new_buffer_dur > old_end and old_end > 0 then
    -- Expanding: tile existing content into the new region.
    -- Copies use preserve=0 (replace) with a short crossfade at boundaries.
    local fade = old_end > 0.01 and 0.002 or 0
    local pos = old_end
    while pos < new_buffer_dur do
      local chunk = math.min(old_end, new_buffer_dur - pos)
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, off, off + pos, chunk, fade, 0)
      end
      pos = pos + chunk
    end
  end

  self.buffer_dur = new_buffer_dur
  self:_apply_loop_end()
end

-- Internal: set softcut loop_end from current state.
-- loop_start is at buffer_offset, loop_end = buffer_offset + buffer_dur.
function Looper:_apply_loop_end()
  self.loop_end_pos = self.buffer_offset + self.buffer_dur
  for _, voice in ipairs(self.voices) do
    softcut.loop_end(voice, self.loop_end_pos)
  end
end

-- Apply isolator via both post_filter (immediate audible kill on output)
-- and pre_filter (prints effect to buffer via feedback path).
-- While iso is active, engine→softcut is cut so only the pre_filtered
-- feedback writes to the buffer. Engine→DAC stays on for live monitoring.
-- On release: both filters return to passthrough; buffer retains printed
-- changes; engine→softcut recording resumes.
-- Softcut's SVF is 12dB/oct, so cutoffs are pushed aggressively.
local ISO_FADE_SECS = 0.010  -- 10ms cutoff frequency sweep
local ISO_FADE_STEPS = 3

function Looper:update_iso(kill_low, kill_mid, kill_high)
  -- Cancel any in-progress fc sweep
  if self._iso_sweep_id then
    clock.cancel(self._iso_sweep_id)
    self._iso_sweep_id = nil
  end

  local n_kills = (kill_low and 1 or 0) + (kill_mid and 1 or 0) + (kill_high and 1 or 0)
  local dry, lp, hp, bp, br, fc, rq = 0, 0, 0, 0, 0, 1000, 2.0

  if n_kills == 0 then
    -- Passthrough
    dry = 1.0
  elseif n_kills == 3 then
    -- Kill everything: silence the feedback
    dry, lp, hp, bp, br = 0, 0, 0, 0, 0
  elseif kill_low and not kill_mid and not kill_high then
    -- Kill low → HP at 500 Hz
    hp = 1.0; fc = 500; rq = 1.4
  elseif not kill_low and kill_mid and not kill_high then
    -- Kill mid → band reject at 935 Hz, wide Q for broad scoop
    br = 1.0; fc = 935; rq = 5.0
  elseif not kill_low and not kill_mid and kill_high then
    -- Kill high → LP at 2000 Hz
    lp = 1.0; fc = 2000; rq = 1.4
  elseif kill_low and kill_mid and not kill_high then
    -- Kill low+mid → pass highs only → HP at 4000 Hz
    hp = 1.0; fc = 4000; rq = 1.4
  elseif kill_low and not kill_mid and kill_high then
    -- Kill low+high → pass mids only → BP at 935 Hz
    bp = 1.0; fc = 935; rq = 3.0
  elseif not kill_low and kill_mid and kill_high then
    -- Kill mid+high → pass lows only → LP at 200 Hz
    lp = 1.0; fc = 200; rq = 1.4
  end

  -- Neutral fc: where this filter type is effectively transparent
  local neutral
  if hp > 0 then neutral = 20
  elseif lp > 0 then neutral = 20000
  elseif br > 0 then neutral = 20000
  elseif bp > 0 then neutral = 20000
  end

  if n_kills == 0 then
    -- Going to passthrough: sweep outgoing filter to its neutral, then switch
    if self._iso_cur_fc and self._iso_cur_neutral then
      local from = self._iso_cur_fc
      local to = self._iso_cur_neutral
      self._iso_sweep_id = clock.run(function()
        self:_iso_sweep_fc(from, to)
        self:_apply_iso_raw(1.0, 0, 0, 0, 0, 1000, 2.0)
        self._iso_sweep_id = nil
      end)
    else
      self:_apply_iso_raw(1.0, 0, 0, 0, 0, 1000, 2.0)
    end
    self._iso_cur_fc = nil
    self._iso_cur_neutral = nil
  elseif neutral and neutral ~= fc then
    -- Engaging a filter: set taps at neutral fc, sweep to target
    self:_apply_iso_raw(dry, lp, hp, bp, br, neutral, rq)
    self._iso_cur_fc = fc
    self._iso_cur_neutral = neutral
    self._iso_sweep_id = clock.run(function()
      self:_iso_sweep_fc(neutral, fc)
      self._iso_sweep_id = nil
    end)
  else
    -- Kill-all or same fc as neutral: apply immediately
    self:_apply_iso_raw(dry, lp, hp, bp, br, fc, rq)
    self._iso_cur_fc = fc
    self._iso_cur_neutral = neutral
  end
end

-- Exponential fc sweep over ISO_FADE_SECS (blocking, call from clock.run)
function Looper:_iso_sweep_fc(from_fc, to_fc)
  local log_from = math.log(from_fc)
  local log_to = math.log(to_fc)
  local step_time = ISO_FADE_SECS / ISO_FADE_STEPS
  for i = 1, ISO_FADE_STEPS do
    clock.sleep(step_time)
    local swept = math.exp(log_from + (log_to - log_from) * (i / ISO_FADE_STEPS))
    for _, voice in ipairs(self.voices) do
      softcut.post_filter_fc(voice, swept)
      softcut.pre_filter_fc(voice, swept)
    end
  end
end

-- Set all filter params immediately (no sweep)
function Looper:_apply_iso_raw(dry, lp, hp, bp, br, fc, rq)
  for _, voice in ipairs(self.voices) do
    softcut.post_filter_dry(voice, dry)
    softcut.post_filter_lp(voice, lp)
    softcut.post_filter_hp(voice, hp)
    softcut.post_filter_bp(voice, bp)
    softcut.post_filter_br(voice, br)
    softcut.post_filter_fc(voice, fc)
    softcut.post_filter_rq(voice, rq)
    softcut.pre_filter_dry(voice, dry)
    softcut.pre_filter_lp(voice, lp)
    softcut.pre_filter_hp(voice, hp)
    softcut.pre_filter_bp(voice, bp)
    softcut.pre_filter_br(voice, br)
    softcut.pre_filter_fc(voice, fc)
    softcut.pre_filter_rq(voice, rq)
  end
end

-- ─── Iso Data Buffer ───
-- Parallel data buffer for per-position filter state, indexed by subdivision
-- (128th notes = 32 per beat). Mirrors audio buffer operations.

function Looper:init_iso_data()
  self.iso_data = {}
  -- No forced passthrough at sub 0: filter holds its current state across
  -- loop boundaries. Events are only created by user interaction.
end

function Looper:iso_total_subs()
  return self.num_beats * ISO_SUBS_PER_BEAT
end

function Looper:clear_iso_data()
  self.iso_data = {}
end

function Looper:clear_iso_data_at(sub)
  self.iso_data[sub] = nil
end

function Looper:get_iso_at(sub)
  return self.iso_data[sub] or {false, false, false}
end

function Looper:set_iso_at(sub, kills)
  self.iso_data[sub] = {kills[1], kills[2], kills[3]}
end

function Looper:_resize_iso_data(old_beats, new_beats)
  if old_beats == new_beats or old_beats == 0 then return end
  local old_total = old_beats * ISO_SUBS_PER_BEAT
  local new_total = new_beats * ISO_SUBS_PER_BEAT
  if new_beats > old_beats then
    -- Tile: repeat sparse events into expanded region
    for i = old_total, new_total - 1 do
      local src = self.iso_data[i % old_total]
      if src then
        self.iso_data[i] = {src[1], src[2], src[3]}
      end
    end
  else
    -- Shrink: drop entries beyond new length
    for i = new_total, old_total - 1 do
      self.iso_data[i] = nil
    end
  end
end

-- ─── Name Data Buffer ───
-- Parallel data buffer for per-position sample names, indexed by subdivision.
-- Same resolution and resize semantics as iso_data.

function Looper:init_name_data()
  self.name_data = {}
end

function Looper:name_total_subs()
  return self.num_beats * ISO_SUBS_PER_BEAT
end

function Looper:clear_name_data()
  self.name_data = {}
end

function Looper:clear_name_data_at(sub)
  self.name_data[sub] = nil
end

function Looper:get_name_at(sub)
  return self.name_data[sub]
end

function Looper:set_name_at(sub, name)
  self.name_data[sub] = name
end

function Looper:_resize_name_data(old_beats, new_beats)
  if old_beats == new_beats or old_beats == 0 then return end
  local old_total = old_beats * ISO_SUBS_PER_BEAT
  local new_total = new_beats * ISO_SUBS_PER_BEAT
  if new_beats > old_beats then
    -- Tile: repeat sparse entries into expanded region
    for i = old_total, new_total - 1 do
      local src = self.name_data[i % old_total]
      if src then
        self.name_data[i] = src
      end
    end
  else
    -- Shrink: drop entries beyond new length
    for i = new_total, old_total - 1 do
      self.name_data[i] = nil
    end
  end
end

-- Start the iso subdivision clock. Fires at 128th note resolution.
-- Checks for stored change events at each sub; when one exists,
-- fires on_iso_tick so erasmus can apply it. Filter holds its
-- state between events (sample-and-hold).
function Looper:start_iso_clock()
  if self.iso_clock_id then clock.cancel(self.iso_clock_id) end
  self.iso_sub = 0
  self.iso_clock_id = clock.run(function()
    while true do
      clock.sync(1 / ISO_SUBS_PER_BEAT)
      if self.playing == 1 then
        local total = self:iso_total_subs()
        if total > 0 then
          self.iso_sub = self.iso_sub % total
          if self.on_sub_tick then
            self.on_sub_tick(self.iso_sub)
          end
          local stored = self.iso_data[self.iso_sub]
          if stored and self.on_iso_tick then
            self.on_iso_tick(self.iso_sub, stored)
          end
          self.iso_sub = self.iso_sub + 1
        end
      end
    end
  end)
end

function Looper:beat_shuffle(group_size)
  if self.staging then return end
  local n = math.floor(self.num_beats / group_size)
  if n < 2 then return end
  local group_dur = group_size * self.buffer_dur / self.num_beats
  local off = self.buffer_offset
  -- Use staging area for temporary storage
  if STAGING_OFFSET + 2 * self.buffer_dur > 350 then return end
  local fade = group_dur > 0.01 and 0.002 or 0
  local offset = self.playhead_pos % self.buffer_dur

  local order = {}
  for i = 1, n do order[i] = i end
  for i = n, 2, -1 do
    local j = math.random(i)
    order[i], order[j] = order[j], order[i]
  end

  for ch = 1, 2 do
    -- Two copies in staging so any offset+group read stays in bounds
    softcut.buffer_copy_mono(ch, ch, off, STAGING_OFFSET, self.buffer_dur, 0, 0)
    softcut.buffer_copy_mono(ch, ch, off, STAGING_OFFSET + self.buffer_dur, self.buffer_dur, 0, 0)

    for dst = 1, n do
      local src_start = offset + (order[dst] - 1) * group_dur
      local dst_start = (offset + (dst - 1) * group_dur) % self.buffer_dur

      if dst_start + group_dur <= self.buffer_dur then
        softcut.buffer_copy_mono(ch, ch,
          STAGING_OFFSET + src_start, off + dst_start, group_dur, fade, 0)
      else
        -- Group wraps around loop boundary: split into two copies
        local first = self.buffer_dur - dst_start
        softcut.buffer_copy_mono(ch, ch,
          STAGING_OFFSET + src_start, off + dst_start, first, fade, 0)
        softcut.buffer_copy_mono(ch, ch,
          STAGING_OFFSET + src_start + first, off, group_dur - first, fade, 0)
      end
    end
  end

  -- Shuffle iso_data segments to match audio (sparse events)
  local subs_per_group = math.floor(group_size * ISO_SUBS_PER_BEAT)
  if subs_per_group > 0 then
    local old_iso = {}
    local total = self:iso_total_subs()
    for i = 0, total - 1 do
      if self.iso_data[i] then
        local src = self.iso_data[i]
        old_iso[i] = {src[1], src[2], src[3]}
      end
    end
    for i = 0, total - 1 do
      self.iso_data[i] = nil
    end
    for dst = 1, n do
      local src_group = order[dst] - 1
      for s = 0, subs_per_group - 1 do
        local di = ((dst - 1) * subs_per_group + s) % total
        local si = (src_group * subs_per_group + s) % total
        if old_iso[si] then
          self.iso_data[di] = old_iso[si]
        end
      end
    end

    -- Shuffle name_data segments to match audio
    local old_names = {}
    for i = 0, total - 1 do
      if self.name_data[i] then
        old_names[i] = self.name_data[i]
      end
    end
    for i = 0, total - 1 do
      self.name_data[i] = nil
    end
    for dst = 1, n do
      local src_group = order[dst] - 1
      for s = 0, subs_per_group - 1 do
        local di = ((dst - 1) * subs_per_group + s) % total
        local si = (src_group * subs_per_group + s) % total
        if old_names[si] then
          self.name_data[di] = old_names[si]
        end
      end
    end
  end
end

function Looper:_apply_rate(slew_time)
  slew_time = slew_time or 0
  local multiplier = 2 ^ (self.pitch_shift_semitones / 12)
  local effective = self.rate * multiplier
  if self.reversed then effective = -effective end
  for _, voice in ipairs(self.voices) do
    softcut.rate_slew_time(voice, slew_time)
    softcut.rate(voice, effective)
  end
end

function Looper:set_pitch_shift(semitones)
  local old = self.pitch_shift_semitones
  self.pitch_shift_semitones = semitones
  local slew = 60 / self.tempo  -- quarter-note slew
  self:_apply_rate(slew)
  -- Iso data is tempo-locked; pitch shift desyncs it from the playhead.
  -- Clear iso data to prevent stale events from replaying and cutting input.
  if semitones ~= old then
    self:clear_iso_data()
  end
end

function Looper:get_effective_rate()
  local r = self.rate * 2 ^ (self.pitch_shift_semitones / 12)
  return self.reversed and -r or r
end

function Looper:set_reversed(rev)
  self.reversed = rev
  self:_apply_rate()
end

function Looper:get_effective_tempo()
  return self.tempo * 2 ^ (self.pitch_shift_semitones / 12)
end

function Looper:request_waveform()
  if self.staging and self.staging_dur > 0 then
    softcut.render_buffer(1, STAGING_OFFSET, self.staging_dur, 128)
  elseif self.buffer_dur > 0 then
    softcut.render_buffer(1, self.buffer_offset, self.buffer_dur, 128)
  end
end

-- Load audio file into staging area (channel 1 only, for waveform preview).
-- Audio playback continues from buffer_offset unchanged.
function Looper:stage_file(filepath, duration)
  self.staging = true
  self.staging_dur = duration
  softcut.buffer_read_mono(filepath, 0, STAGING_OFFSET, duration, 1, 0)
end

-- Commit staged file: re-read from disk into both softcut buffers at buffer_offset.
-- Uses buffer_read_mono (not buffer_read_stereo) so mono sample files load correctly.
function Looper:commit_staging(filepath, duration)
  self.staging = false
  self.staging_dur = 0
  softcut.buffer_read_mono(filepath, 0, self.buffer_offset, duration, 1, 0)
  softcut.buffer_read_mono(filepath, 0, self.buffer_offset, duration, 2, 0)
end

-- Cancel staging: clear flag, no buffer changes needed (staging area is ignored).
function Looper:cancel_staging()
  self.staging = false
  self.staging_dur = 0
end

function Looper:jump_to_position(fraction)
  local pos = fraction * self.buffer_dur
  for _, voice in ipairs(self.voices) do
    softcut.position(voice, self.buffer_offset + pos)
  end
  -- Sync beat counter to match the new playhead position
  self.cur_beat = math.floor(fraction * self.num_beats)
end

-- Begin direct-to-buffer recording. Softcut already receives the engine
-- input in real-time — we just clear the buffer region, park the playhead at
-- buffer_offset, open up a long recording region, and zero pre_level so old
-- content doesn't bleed through. The capturing flag guards routing and resize.
function Looper:start_recording()
  self.capturing = true
  self.capture_start_time = util.time()
  -- Clear this track's region and set up linear recording space
  softcut.buffer_clear_region(self.buffer_offset, self.region_size)
  for _, voice in ipairs(self.voices) do
    softcut.loop_end(voice, self.buffer_offset + self.region_size)
    softcut.position(voice, self.buffer_offset)
    softcut.pre_level(voice, 0)
  end
end

-- End direct-to-buffer recording. Returns recorded duration.
function Looper:stop_recording()
  self.capturing = false
  local duration = math.min(util.time() - self.capture_start_time, self.region_size)
  duration = math.max(duration, 0.5)
  return duration
end

function Looper:begin_batch()
  self._batch = true
end

function Looper:end_batch()
  self._batch = false
  self.loop_dur = (self.num_beats / self.tempo) * 60
  -- Check if buffer needs resize (beat change within batch)
  local target = self.rate * self.loop_dur
  if math.abs(target - self.buffer_dur) > 0.001 then
    self:_resize_buffer(target)
  end
  -- Recompute rate from final state
  self.rate = self.buffer_dur / self.loop_dur
  self:_apply_rate()
end

function Looper:get_buffer_dur()
  return self.buffer_dur
end

function Looper:get_rate()
  return self.rate
end

Looper.ISO_SUBS_PER_BEAT = ISO_SUBS_PER_BEAT

return Looper
