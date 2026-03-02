-- lib/looper.lua
-- Erasmus softcut looper module
-- Adapted from samsara v1.4.3 by @21echoes
-- Two softcut voices (1=L, 2=R) forming a stereo delay loop
-- Isolator uses post_filter (immediate audible kill) + pre_filter (prints to buffer).
-- While iso is active, engine→softcut is cut so unfiltered input can't contaminate
-- the buffer — only the pre_filtered feedback path writes back.
--
-- Uses softcut native looping for sample-accurate timing.
-- The clock coroutine only drives the UI beat counter.
--
-- Delay-line model: loop_start is fixed at 0, loop_end = delay time.
-- Changing beats/tempo just moves loop_end. pre_level is feedback,
-- rec_level is input mix. On resize, buffer content is rearranged
-- to preserve the most recently heard output. Softcut handles the rest.

local Looper = {}
Looper.__index = Looper

local MAX_NUM_BEATS = 32
local STAGING_OFFSET = 175  -- staging area at [175, 350], safe from loop content at [0, buffer_dur]
local ISO_SUBS_PER_BEAT = 32  -- 128th note resolution for iso data buffer
-- Engine attenuation: instead of boosting softcut output (which bakes into
-- tape bounces), we attenuate the engine on both paths (monitoring + recording)
-- so that softcut playback at unity matches the engine. Tape-stable.
local ENG_LEVEL = 1 / 1.4

function Looper.new()
  local self = setmetatable({}, Looper)
  self.playing = 1
  self.rec_level = 1.0
  self.pre_level = 1.0
  self.num_beats = 8
  self.tempo = 120
  self.loop_dur = (8 / 120) * 60 -- default
  self.loop_start_pos = 0        -- buffer position of loop start (always 0)
  self.loop_end_pos = 0          -- buffer position of loop end (set in init)
  self.playhead_pos = 0          -- tracked via phase polling
  self.cur_beat = 0
  self.clock_id = nil
  self.on_beat_callback = nil
  self.buffer_muted = false
  self.solo_mode = false
  self.rate = 1.0
  self.buffer_dur = 0          -- set in init(), tracks actual buffer content length
  self._batch = false          -- true during atomic tempo+beats updates
  self.pitch_shift_semitones = 0
  self.waveform_brightness = {} -- 16-element brightness cache
  self.on_waveform_callback = nil
  self.capturing = false
  self.staging = false
  self.staging_dur = 0
  self.iso_data = {}           -- sparse change events: iso_data[sub] = {low, mid, high} or nil
  self.iso_sub = 0             -- current subdivision counter (0-based)
  self.iso_clock_id = nil
  self.on_iso_tick = nil       -- callback(sub, kills) fired when a stored event is reached
  self._iso_sweep_id = nil     -- clock id for in-progress fc sweep
  self._iso_cur_fc = nil       -- last target fc (for sweeping back to neutral)
  self._iso_cur_neutral = nil  -- neutral fc for current filter type

  -- Audio level state for restore
  self.initial_levels = {}
  self.modified_level_params = {
    "cut_input_adc",
    "cut_input_eng",
    "cut_input_tape",
    "monitor_level",
    "softcut_level",
  }
  return self
end

function Looper:init()
  -- Save initial audio levels before we modify them
  for _, level_param in ipairs(self.modified_level_params) do
    self.initial_levels[level_param] = params:get(level_param)
  end

  -- Reset ALL softcut state to known defaults. Critical: without this,
  -- stale parameters from a previously-run script persist in the C audio
  -- thread across script reloads (filter coefficients, fade_time,
  -- inter-voice routing, etc.). softcut.reset() is the only way to
  -- guarantee a clean slate.
  softcut.reset()

  -- Audio routing — params for norns LEVELS menu integration,
  -- direct audio.* calls as belt-and-suspenders backup.
  audio.level_eng(ENG_LEVEL)                  -- Engine -> DAC (attenuated to match softcut at unity)
  self:_refresh_eng_cut()                    -- Engine -> softcut (respects solo/iso state)
  params:set("cut_input_adc", -math.huge)    -- ADC -> softcut OFF
  params:set("cut_input_tape", -math.huge)   -- Tape -> softcut OFF
  params:set("monitor_level", -math.huge)    -- ADC -> DAC OFF
  params:set("softcut_level", 0)             -- Softcut -> DAC ON (0 dB)
  audio.level_cut(1)                         -- (direct: linear 1.0 = 0 dB)

  softcut.buffer_clear()

  self.loop_start_pos = 0

  for voice = 1, 2 do
    softcut.enable(voice, 1)
    softcut.buffer(voice, voice)
    softcut.pan(voice, voice == 1 and -1.0 or 1.0)
    softcut.rate(voice, 1)
    -- Native looping for sample-accurate wrap
    softcut.loop(voice, 1)
    softcut.loop_start(voice, 0)
    softcut.position(voice, 0)
    -- Route softcut input bus stereo into voices: L->voice1, R->voice2
    softcut.level_input_cut(1, voice, voice == 1 and 1.0 or 0.0)
    softcut.level_input_cut(2, voice, voice == 2 and 1.0 or 0.0)
    softcut.level(voice, 1.0)
    softcut.pre_level(voice, self.pre_level)
    softcut.rec_level(voice, self.rec_level)
    -- Short slew on rec/pre to avoid clicks but stay punchy
    softcut.level_slew_time(voice, 0.01)
    softcut.recpre_slew_time(voice, 0.01)
    softcut.rec(voice, 1)
    softcut.play(voice, 1)
  end

  -- Both filters to passthrough. softcut.reset() defaults pre_filter_dry
  -- to 0.0 (blocks all feedback), so we MUST set dry=1.0 here.
  for voice = 1, 2 do
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

  -- Phase polling to track playhead for content-preserving resize
  local this = self
  softcut.event_phase(function(voice, pos)
    if voice == 1 then
      this.playhead_pos = pos
    end
  end)
  softcut.phase_quant(1, 1/30)

  -- Waveform render callback: bins 128 samples into 16 groups, peak per bin,
  -- then normalizes brightness relative to the loudest bin.
  softcut.event_render(function(ch, start, sec_per_sample, samples)
    if ch ~= 1 then return end
    local n = #samples
    local bin_size = math.floor(n / 16)
    if bin_size < 1 then bin_size = 1 end
    local peaks = {}
    local max_peak = 0
    for bin = 1, 16 do
      local peak = 0
      local lo = (bin - 1) * bin_size + 1
      local hi = (bin == 16) and n or (bin * bin_size)
      for i = lo, hi do
        local v = math.abs(samples[i] or 0)
        if v > peak then peak = v end
      end
      peaks[bin] = peak
      if peak > max_peak then max_peak = peak end
    end
    for bin = 1, 16 do
      if max_peak > 0 then
        this.waveform_brightness[bin] = math.floor((peaks[bin] / max_peak) * 15 + 0.5)
      else
        this.waveform_brightness[bin] = 0
      end
    end
    if this.on_waveform_callback then
      this.on_waveform_callback()
    end
  end)

  -- Set initial loop_end
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self.buffer_dur = self.loop_dur
  self.rate = 1.0
  self:_apply_loop_end()
  self:_apply_rate()

  self:init_iso_data()

  print("looper: init complete — eng->cut ON, cut->dac ON, loop=" ..
    string.format("%.2fs", self.loop_dur))
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
  for voice = 1, 2 do
    softcut.pre_level(voice, val)
  end
end

function Looper:set_rec_level(val)
  self.rec_level = val
  if not self.buffer_muted then
    for voice = 1, 2 do
      softcut.rec_level(voice, val)
    end
  end
end

function Looper:set_num_beats(val)
  local old_beats = self.num_beats
  self.num_beats = util.clamp(val, 1, MAX_NUM_BEATS)
  self.loop_dur = (self.num_beats / self.tempo) * 60
  if self._batch then return end
  -- Resize buffer to maintain current rate
  local new_buffer_dur = self.rate * self.loop_dur
  self:_resize_buffer(new_buffer_dur)
  self:_resize_iso_data(old_beats, self.num_beats)
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
    for voice = 1, 2 do
      softcut.enable(voice, 1)
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
    for voice = 1, 2 do
      softcut.rec_level(voice, 0.0)
      softcut.level(voice, 0.0)
      softcut.enable(voice, 0)
    end
    self.playing = 0
  end
end

function Looper:set_buffer_muted(muted)
  self.buffer_muted = muted
  for voice = 1, 2 do
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
  for voice = 1, 2 do
    softcut.level(voice, muted and 0 or 1.0)
  end
end

function Looper:clear_buffer()
  softcut.buffer_clear()
end

function Looper:load_state(bpm, beats)
  self.tempo = bpm
  self.num_beats = util.clamp(beats, 1, MAX_NUM_BEATS)
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self.buffer_dur = self.loop_dur
  self.rate = 1.0
  self:_apply_loop_end()
  self:_apply_rate()
  for voice = 1, 2 do
    softcut.position(voice, 0)
  end
  self:init_iso_data()
  self.iso_sub = 0
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

  -- Restore prior audio levels
  for level_param, level in pairs(self.initial_levels) do
    params:set(level_param, level)
  end
end

-- Content-preserving buffer resize.
-- On shrink: copies the most recently heard content to [0, new_buffer_dur].
-- On expand: tiles existing content to fill [old_dur, new_buffer_dur].
-- Blocked during capture to protect the staging area.
function Looper:_resize_buffer(new_buffer_dur)
  if self.capturing or self.staging then return end
  local old_end = self.buffer_dur

  if new_buffer_dur < old_end and old_end > 0 then
    -- Shrinking: preserve the last new_buffer_dur seconds of output.
    -- That content lives at [P - new_buffer_dur, P] in the old buffer (wrapping).
    local p = self.playhead_pos
    local src = p - new_buffer_dur
    if src >= 0 then
      -- No wrap: forward copy is safe (dst=0 < src)
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, src, 0, new_buffer_dur, 0, 0)
      end
    else
      -- Wrap: assemble in staging area to avoid overlap
      local staging = self.buffer_dur
      local wrap_src = old_end + src
      local first_len = old_end - wrap_src
      local second_len = new_buffer_dur - first_len
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, wrap_src, staging, first_len, 0, 0)
        if second_len > 0 then
          softcut.buffer_copy_mono(ch, ch, 0, staging + first_len, second_len, 0, 0)
        end
        softcut.buffer_copy_mono(ch, ch, staging, 0, new_buffer_dur, 0, 0)
      end
    end
    -- Don't reposition playhead — softcut wraps it naturally when
    -- loop_end moves inward, preserving timing continuity.
  elseif new_buffer_dur > old_end and old_end > 0 then
    -- Expanding: clear the new region first (removes stale content),
    -- then tile existing content into it. Both are async softcut
    -- commands so they execute in order on the audio thread.
    softcut.buffer_clear_region(old_end, new_buffer_dur - old_end)
    local pos = old_end
    while pos < new_buffer_dur do
      local chunk = math.min(old_end, new_buffer_dur - pos)
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, 0, pos, chunk, 0, 0)
      end
      pos = pos + chunk
    end
  end

  self.buffer_dur = new_buffer_dur
  self:_apply_loop_end()
end

-- Internal: set softcut loop_end from current state.
-- loop_start is always 0, loop_end = buffer_dur (buffer-space wrap point).
function Looper:_apply_loop_end()
  self.loop_end_pos = self.buffer_dur
  for voice = 1, 2 do
    softcut.loop_end(voice, self.loop_end_pos)
  end
end

-- Centralized engine→softcut routing. Cut when solo mode is active.
-- During capture/recording, always keep routing ON so recording isn't interrupted.
function Looper:_refresh_eng_cut()
  if self.capturing then return end
  if self.solo_mode then
    params:set("cut_input_eng", -math.huge)
    audio.level_eng_cut(0)
  else
    params:set("cut_input_eng", 20 * math.log(ENG_LEVEL, 10))
    audio.level_eng_cut(ENG_LEVEL)
  end
end

function Looper:set_solo_mode(val)
  self.solo_mode = val
  self:_refresh_eng_cut()
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
  -- HP@20 passes everything, LP@20k passes everything,
  -- BR@20k rejects nothing audible, BP@20k is brief inaudible blip
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
    for voice = 1, 2 do
      softcut.post_filter_fc(voice, swept)
      softcut.pre_filter_fc(voice, swept)
    end
  end
end

-- Set all filter params immediately (no sweep)
function Looper:_apply_iso_raw(dry, lp, hp, bp, br, fc, rq)
  for voice = 1, 2 do
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
  self.iso_data[0] = {false, false, false}  -- loop boundary: reset to passthrough
end

function Looper:iso_total_subs()
  return self.num_beats * ISO_SUBS_PER_BEAT
end

function Looper:clear_iso_data()
  self.iso_data = {}
  self.iso_data[0] = {false, false, false}
end

function Looper:clear_iso_data_at(sub)
  if sub == 0 then
    self.iso_data[0] = {false, false, false}  -- sub 0 always exists (loop boundary reset)
  else
    self.iso_data[sub] = nil
  end
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
  local staging = self.buffer_dur
  -- Double-copy staging so wrapped reads are contiguous
  if staging + 2 * self.buffer_dur > 350 then return end
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
    softcut.buffer_copy_mono(ch, ch, 0, staging, self.buffer_dur, 0, 0)
    softcut.buffer_copy_mono(ch, ch, 0, staging + self.buffer_dur, self.buffer_dur, 0, 0)

    for dst = 1, n do
      local src_start = offset + (order[dst] - 1) * group_dur
      local dst_start = (offset + (dst - 1) * group_dur) % self.buffer_dur

      if dst_start + group_dur <= self.buffer_dur then
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start, dst_start, group_dur, fade, 0)
      else
        -- Group wraps around loop boundary: split into two copies
        local first = self.buffer_dur - dst_start
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start, dst_start, first, fade, 0)
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start + first, 0, group_dur - first, fade, 0)
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
  end
end

function Looper:_apply_rate(slew_time)
  slew_time = slew_time or 0
  local multiplier = 2 ^ (self.pitch_shift_semitones / 12)
  local effective = self.rate * multiplier
  for voice = 1, 2 do
    softcut.rate_slew_time(voice, slew_time)
    softcut.rate(voice, effective)
  end
end

function Looper:set_pitch_shift(semitones)
  self.pitch_shift_semitones = semitones
  local slew = 60 / self.tempo  -- quarter-note slew
  self:_apply_rate(slew)
end

function Looper:get_effective_rate()
  return self.rate * 2 ^ (self.pitch_shift_semitones / 12)
end

function Looper:get_effective_tempo()
  return self.tempo * 2 ^ (self.pitch_shift_semitones / 12)
end

function Looper:request_waveform()
  if self.staging and self.staging_dur > 0 then
    softcut.render_buffer(1, STAGING_OFFSET, self.staging_dur, 128)
  elseif self.buffer_dur > 0 then
    softcut.render_buffer(1, 0, self.buffer_dur, 128)
  end
end

-- Load audio file into staging area (channel 1 only, for waveform preview).
-- Audio playback continues from position 0 unchanged.
function Looper:stage_file(filepath, duration)
  self.staging = true
  self.staging_dur = duration
  softcut.buffer_read_mono(filepath, 0, STAGING_OFFSET, duration, 1, 0)
end

-- Commit staged file: re-read from disk into both softcut buffers at position 0.
-- Uses buffer_read_mono (not buffer_read_stereo) so mono sample files load correctly.
function Looper:commit_staging(filepath, duration)
  self.staging = false
  self.staging_dur = 0
  softcut.buffer_read_mono(filepath, 0, 0, duration, 1, 0)
  softcut.buffer_read_mono(filepath, 0, 0, duration, 2, 0)
end

-- Cancel staging: clear flag, no buffer changes needed (staging area is ignored).
function Looper:cancel_staging()
  self.staging = false
  self.staging_dur = 0
end

function Looper:jump_to_position(fraction)
  local pos = fraction * self.buffer_dur
  for voice = 1, 2 do
    softcut.position(voice, pos)
  end
end

-- Begin direct-to-buffer recording. Softcut already receives the engine
-- input in real-time — we just clear the buffer, park the playhead at 0,
-- open up a long recording region, and zero pre_level so old content
-- doesn't bleed through. The capturing flag guards routing and resize.
function Looper:start_recording()
  self.capturing = true
  self.capture_start_time = util.time()
  -- Force engine → softcut routing on (in case solo/iso was active)
  params:set("cut_input_eng", 20 * math.log(ENG_LEVEL, 10))
  audio.level_eng_cut(ENG_LEVEL)
  -- Clear and set up linear recording space
  softcut.buffer_clear()
  for voice = 1, 2 do
    softcut.loop_end(voice, 175)
    softcut.position(voice, 0)
    softcut.pre_level(voice, 0)
  end
end

-- End direct-to-buffer recording. Returns recorded duration.
function Looper:stop_recording()
  self.capturing = false
  local duration = math.min(util.time() - self.capture_start_time, 175)
  duration = math.max(duration, 0.5)
  self:_refresh_eng_cut()
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

return Looper
