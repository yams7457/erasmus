-- lib/screen_ui.lua
-- Norns screen drawing: 3-column scrolling name display.
--
-- Each column shows one track's name_data buffer, scrolling at the iso
-- tick rate (1/128 note). The current playhead position is at the top,
-- with upcoming content below. Every sub gets a row — nil subs are blank,
-- so the display scrolls smoothly with the playhead.

local ScreenUI = {}

local Looper -- set by init

-- Module-level reference to shared state (set by init)
local S

function ScreenUI.init(state, looper_module)
  S = state
  Looper = looper_module
end

-- Full-width 3-column layout (128px / 3 ≈ 42px each)
local COL_X = {1, 44, 87}
local NAME_MAX_CHARS = 7
local ROW_H = 8
local NUM_ROWS = 8       -- 64px screen / 8px per row

-- Per-track brightness: top row (current) and dim (upcoming)
local COL_BRIGHT = {15, 9, 5}
local COL_DIM = {8, 5, 3}

function ScreenUI.redraw()
  -- Don't paint over the norns system menu
  if _menu and _menu.mode then return end
  screen.clear()
  screen.font_size(8)

  -- Rec state indicator in top-right corner
  if S.rec_state == "armed" then
    screen.level(15)
    screen.move(126, 8)
    screen.text_right("ARM")
  elseif S.rec_state == "recording" then
    screen.level(15)
    screen.move(126, 8)
    screen.text_right("REC")
  end

  -- 3 columns: 8 rows evenly spaced across the full loop.
  -- Row 1 = current playhead position, rows 2-8 = upcoming content.
  -- Stride = total_subs / 8 so you see the whole loop at a glance.
  for ti = 1, 3 do
    local t = S.tracks[ti]
    local total = t:name_total_subs()
    if total > 0 then
      local cur = t.iso_sub % total
      local x = COL_X[ti]
      local bright = COL_BRIGHT[ti]
      local dim = COL_DIM[ti]
      local stride = math.max(1, math.floor(total / NUM_ROWS))

      for r = 1, NUM_ROWS do
        local sub = (cur + (r - 1) * stride) % total
        local name = t.name_data[sub]
        if name then
          local display = name
          if #display > NAME_MAX_CHARS then
            display = display:sub(1, NAME_MAX_CHARS)
          end
          screen.level(r == 1 and bright or dim)
          screen.move(x, r * ROW_H)
          screen.text(display)
        end
      end
    end
  end

  screen.update()
end

function ScreenUI.frame_tick()
  local any_playing = false
  for i = 1, 3 do
    if S.tracks[i]:get_playing() == 1 then any_playing = true; break end
  end
  if any_playing or S.is_screen_dirty then
    S.is_screen_dirty = false
    ScreenUI.redraw()
  end
end

return ScreenUI
