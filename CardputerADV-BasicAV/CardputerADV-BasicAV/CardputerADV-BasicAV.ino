/*
 * CardputerADV-BasicAV v1.0 — M5Stack Cardputer ADV (ESP32-S3, ES8311 via M5Unified, TCA8418 keyboard).
 * BUILD THIS SKETCH: open the inner CardputerADV-BasicAV folder that contains this .ino
 *   (path ends …/CardputerADV-BasicAV/CardputerADV-BasicAV/CardputerADV-BasicAV.ino).
 * Base Cardputer (GPIO matrix) is not supported here: key coordinates, Tab/Enter handling, and audio path are tuned for ADV.
 *
 * MJPEG (+ optional .pcm), MP3, file menu, seek, loop. SD root: .mjpeg / .mjpg (+ optional .pcm) and/or .mp3
 *
 * Browser: S/s on a highlighted file marks it and runs the pre-play countdown (seconds from D editor if D>0,
 *   else kTimerPlayDefaultDelaySec), then plays—repeatable after every return from playback.
 *   Enter opens folders or plays media immediately (no countdown). D = delay editor. C = countdown HUD toggle.
 *   Tab (physical): go up one folder in the list; during pre-play, Tab/Esc cancels countdown. During playback,
 *   S still bookmarks the current file for the HUD. H: shortcuts overlay (~9s, H again closes early).
 * Video: P or BtnA pause; Tab/Esc = menu; , / or arrows seek; L/A as above; - = vol.
 * MP3: V cycles viz (bars / ducks / matrix / wave / tape still); tape uses SD splash PNGs (magnetic1 first) or embedded splash. , / seek; N/B next/prev folder. Top-right = elapsed/total when known.
 * Hold 0 or i ~0.05s: system info (battery, etc.); release to resume. Audio is muted for that screen so the long draw cannot I2S-underrun (buzz). Overlay draws once; light poll while held.
 * Startup splash: SD tries tape-o-magnetic1.png (or tape-o-megnetic1.png) then tape-o-magnetic.png; embedded fallback
 * tape_o_magnetic_splash_png.h;
 * stretch toward
 * full panel, slight inset (~40%), centered; captions drawn on top.
 * Optional root SD clip /startTape.mp3 during splash (see kSplashJinglePath).
 *
 * MP3 needs: ESP8266Audio. AnimatedGIF (bitbank2) is bundled as AnimatedGIF.cpp / .h / gif.inl next to this sketch.
 * MP3 I2S: AudioOutputMeterI2S::begin() overrides ESP8266Audio to use I2S_NUM_1 (SPK_I2S_PORT) instead of
 * I2S_NUM_AUTO, and avoids assert() on alloc failure — fixes Tab→next MP3 reboot on Cardputer ADV.
 *
 * Convert video: see `scripts/mp4_to_cardputer_mjpeg.sh` in full project trees, or run e.g.:
 *   ffmpeg -y -i Your.mp4 -vf "scale=240:135:force_original_aspect_ratio=increase,crop=240:135" -r 15 -q:v 8 -an Your.mjpeg
 *   ffmpeg -y -i Your.mp4 -map 0:a:0 -f u8 -acodec pcm_u8 -ar 44100 -ac 1 Your.pcm
 */

#include <SPI.h>
#include <SD.h>
#include <algorithm>
#include <cstring>
#include <string.h>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <M5Cardputer.h>
#if defined(ESP_PLATFORM)
#include <esp_heap_caps.h>
#include <esp_random.h>
#endif
#include "MjpegClass.h"

#include "AudioFileSourceSD.h"
#include "AudioGeneratorMP3.h"
#include "AudioOutputI2S.h"
#include "splash_duck_rgb565.h"
#include "tape_o_magnetic_splash_png.h"
#include "tape_o_magnetic1_splash_png.h"
#include "AnimatedGIF.h"
#include <math.h>

// Types must come before any static functions: Arduino inserts function prototypes right after #includes,
// so listMediaDir / pollMenuKeys / playMp3File prototypes would otherwise see these names undefined.
enum class MenuAction {
  NONE,
  ENTER,
  UP,
  DOWN,
  TOGGLE_LOOP,
  UP_DIR,
  TOGGLE_AUTOPLAY,
  TIMER_PLAY_FILE,
  OPEN_DELAY_EDITOR,
  TOGGLE_COUNTDOWN_HUD,
  SHOW_KEYS_HINT,
};

enum class PlayExit { MENU, TRACK_FINISHED, TRACK_NEXT, TRACK_PREV };

struct MediaEntry {
  String label;
  String fullPath;
  bool isDir;
};

static void drawBrowser(const String &cwd, const std::vector<MediaEntry> &entries, int sel, int &scroll,
                        bool listRegionOnly);

enum class PlayKey {
  NONE,
  BACK_MENU,
  PAUSE_TOGGLE,
  SEEK_LEFT,
  SEEK_RIGHT,
  TOGGLE_LOOP,
  TOGGLE_AUTOPLAY,
  TRACK_NEXT,
  TRACK_PREV,
  S_SET_MEDIA,
  SHOW_KEYS_HINT,
};

enum class Mp3VizMode : uint8_t { BARS = 0, DUCK_STILL, DUCK_DANCE, MATRIX, WAVE, TAPE_STILL };

static constexpr uint8_t MP3_VIZ_MODE_COUNT = 6;

static constexpr int TARGET_FPS = 15;
static constexpr uint32_t FRAME_MS = 1000 / TARGET_FPS;
static constexpr unsigned AUDIO_RATE = 44100;
static constexpr size_t AUDIO_CHUNK = AUDIO_RATE / static_cast<unsigned>(TARGET_FPS);
// Video (MJPEG): forward /? step ≈ 5 s; ,< backward is longer (reopen+skip is costly; users expect a
// bigger rewind per tap than a symmetric 5 s).
static constexpr int SEEK_FRAMES = TARGET_FPS * 5;
static constexpr int SEEK_BACK_FRAMES = TARGET_FPS * 12;

static constexpr uint8_t HID_LEFT = 0x50;
static constexpr uint8_t HID_RIGHT = 0x4F;
static constexpr uint8_t HID_UP = 0x52;
static constexpr uint8_t HID_DOWN = 0x51;
static constexpr uint8_t HID_ESC = 0x29;  // USB keyboard Escape

static constexpr int SD_SPI_SCK_PIN = 40;
static constexpr int SD_SPI_MISO_PIN = 39;
static constexpr int SD_SPI_MOSI_PIN = 14;
static constexpr int SD_SPI_CS_PIN = 12;

// M5 Cardputer ADV internal speaker (M5Unified: I2S_NUM_1, BCLK/LRCLK/DOUT = 41/43/42)
static constexpr int SPK_I2S_PORT = 1;
static constexpr int SPK_PIN_BCLK = 41;
static constexpr int SPK_PIN_LRCLK = 43;
static constexpr int SPK_PIN_DOUT = 42;

static constexpr size_t MJPEG_BUFFER_SIZE = (240 * 134 * 2 / 4);
static constexpr int MENU_LINES = 6;
static constexpr int LINE_H = 14;
// MP3: header text uses y < MP3_VIS_TOP; loop hint uses last MP3_VIS_BOTTOM_MARGIN px.
static constexpr int MP3_VIS_TOP = 38;
static constexpr int MP3_VIS_BOTTOM_MARGIN = 14;
static constexpr uint32_t kMp3PauseToggleDebounceMs = 450;
static constexpr int kSpeakerVolumeStep = 5;
static constexpr int kStartupVolumePct = 20;
// Splash: play from SD card root (keeps flash free; small runtime heap only for decoder/I2S).
static const char *const kSplashJinglePath = "/startTape.mp3";
static constexpr uint32_t kSplashJingleMaxMs = 20000u;
// Splash: tape-o-magnetic1.png first, then tape-o-magnetic.png — root and /assets/ (mixed case).
static const char *const kSplashImagePngPaths[] = {
    "/tape-o-magnetic1.png",         "/tape-o-magnetic1.PNG",         "/assets/tape-o-magnetic1.png",
    "/assets/tape-o-magnetic1.PNG", "/Assets/tape-o-magnetic1.png", "/Assets/tape-o-magnetic1.PNG",
    "/tape-o-megnetic1.png",         "/tape-o-megnetic1.PNG",         "/assets/tape-o-megnetic1.png",
    "/assets/tape-o-megnetic1.PNG", "/Assets/tape-o-megnetic1.png", "/Assets/tape-o-megnetic1.PNG",
    "/tape-o-magnetic.png",         "/tape-o-magnetic.PNG",         "/assets/tape-o-magnetic.png",
    "/assets/tape-o-magnetic.PNG", "/Assets/tape-o-magnetic.png", "/Assets/tape-o-magnetic.PNG"};
static constexpr size_t kSplashImagePngPathCount = sizeof(kSplashImagePngPaths) / sizeof(kSplashImagePngPaths[0]);
// Matrix backup for top row: _key_value_map row 0 has '-' at x=10, '=' at x=11 (x=12 is Backspace). If
// your unit’s wiring matches the swapped keycaps vs this map, set true (then x=11 is "down", x=10 "up").
static constexpr bool kVolumeMinusPlusMatrixColsSwapped = true;

static MjpegClass g_mjpeg;
static uint8_t *g_mjpegBuf = nullptr;
static uint8_t *g_audioBuf = nullptr;

// Loop current file (MJPEG or MP3) when it ends
static bool g_loopEnabled = false;
// After a track ends: play next file in same folder (no wrap past last file)
static bool g_folderAutoplay = false;

static bool g_keysHintOpen = false;
static bool g_keysHintPainted = false;
static bool g_keysHintNeedFullUiRedraw = false;
static void showKeysHintNow();
static void keysHintOnHKey(bool *pBrowserNeedRedraw);
static void clearKeysHintForMedia();
static void drawKeysHintOverlayTick(bool *pBrowserNeedRedraw);

static uint32_t g_mp3VolHintUntil = 0;
static bool g_mp3VolHintActive = false;
static uint32_t g_mp3LoopHintUntil = 0;
static bool g_mp3LoopHintActive = false;
static bool g_mp3LoopHintState = false;

static uint32_t g_setBookmarkHintUntil = 0;
static bool g_setBookmarkHintActive = false;
static bool g_setBookmarkHintIsSet = false;

// Volume UI can cause short keyboard ghosting on ADV; if we see a "p" toggle during
// that window, ignore it to prevent accidental pause when changing volume.
static uint32_t g_ignorePauseToggleUntilMs = 0;
// Guard against one physical V press producing multiple visual edges under ADV ghost/bounce.
static uint32_t g_lastVizToggleMs = 0;
static constexpr uint32_t kMp3VizToggleDebounceMs = 110u;
// Cross-lock: after P, briefly ignore V (and vice versa via g_ignorePauseToggleUntilMs).
static uint32_t g_ignoreVizToggleUntilMs = 0;
// Last user speaker level (0–255); survives MP3 I2S teardown and track changes (restore used to reset to session-start vol).
static int g_speakerVolumePersist = kStartupVolumePct * 255 / 100;

// Matrix viz timing — must appear before mp3PollAllKeys (Arduino injects prototypes; later statics are out of scope there).
static uint32_t g_mp3MatrixLastAdvanceMs = 0;
static uint16_t g_mp3MatrixStepIntervalMs = 130;  // smaller = faster; ↑/↓ while Matrix viz

static void setSpeakerVolumePersisted(int v) {
  v = constrain(v, 0, 255);
  g_speakerVolumePersist = v;
  M5Cardputer.Speaker.setVolume(v);
}

// When volume changes, some ADV units can momentarily report unrelated keys
// (ghosting). Suppress seek commands briefly so video doesn't appear to restart.
static uint32_t g_lastVolumeStepMs = 0;
static constexpr uint32_t kVolumeGhostSuppressSeekMs = 140u;

// After Tab/Esc exits MP3/video, the key can still be down; ignore UP_DIR from Tab/Esc until released (avoids WDT/spurious nav).
static bool g_menuSuppressTabEscUpDir = false;
// After exiting playback, Enter can remain electrically "stuck" and re-open MP3/video if the guard
// drops while still held (fixed 350 ms timeout used to do that → menu blink / reopen loop).
static bool g_menuSuppressEnterUntilRelease = false;
static uint32_t g_menuSuppressEnterArmMs = 0;
// Playback: clear when Enter releases, or ~550 ms watchdog so a stuck matrix read cannot lock Enter forever.
static bool g_menuSuppressEnterPlayback = false;
static bool g_menuSyncEnterEdgeOnNextPoll = false;
static uint32_t g_menuLastEnterAtMs = 0;
static constexpr uint32_t kMenuEnterMinGapMs = 180u;
// When D-delay is 0, T still runs a visible pre-play countdown (seconds).
// Browser S countdown when play-start delay (D) is 0.
static constexpr uint32_t kTimerPlayDefaultDelaySec = 5u;
// After exiting playback, some punctuation/bracket keys can remain electrically "stuck"
// in the keyboard reader for a frame or two. Reset edge-detection baselines so the
// browser list doesn't appear to hang.
static bool g_menuResetListNavEdgesOnNextPoll = false;
// pollMenuKeys is not called during pre-play or media playback; S/D/C edge state can stay latched.
static bool g_menuResetBrowserLetterTogglesOnNextPoll = false;
// Browser S=timer play (tap/edge). Cooldown between list triggers so matrix/word noise cannot spam
// TIMER_PLAY_FILE every poll (that skipped UP/DOWN and froze the selector).
static uint32_t g_browserTimerPlayLastMs = 0;
static constexpr uint32_t kBrowserListTimerPlayCooldownMs = 320u;
// Main file-list loop: rising edge for H→hint toggle (pollMenuKeys runs after S/timer logic).
static bool g_browserMainListHKeyPrev = false;
// FIFO edge + relaxed matrix edge; s_browserHintHFifoPrev debounces pressEvents.
static bool s_browserHintHFifoPrev = false;
// After keysHintOnHKey toggles overlay, snap baselines so stuck (7,2) in keyList does not block repeats.
static bool s_browserHintResyncHBaselineNextPoll = false;
static bool g_browserTimerPlaySPrevHeld = false;
// After playback / UI hop, sync Tab→UP_DIR edge baseline so st.word ghosts don't spam redraws.
static bool g_menuSyncTabEscBackBaselineOnNextPoll = false;
// Tab suppress: use physical Tab / HID Esc only. Including st.word \\t/ESC kept suppress stuck (keys
// felt dead) and could still fake UP_DIR after release.
static uint32_t g_menuTabSuppressArmMs = 0;
static constexpr uint32_t kMenuTabSuppressForceReleaseMs = 700u;
static uint32_t g_menuLastBrowserUpDirMs = 0;
static constexpr uint32_t kMenuBrowserUpDirMinGapMs = 220u;
// Browser: Tab down edge → UP_DIR (go up one folder). Countdown on files is S only.
static bool s_menuTabWasDown = false;
// Full-screen countdown before opening a file (not dirs). 0 = off; max 24h. D/d opens delay editor in browser.
static constexpr uint32_t kPlayStartDelayMaxSec = 86400u;  // 24 * 3600
static uint32_t g_playStartDelaySec = 0;
static bool g_playStartCountdownHudVisible = false;
static bool g_playDelayEditOpen = false;
static uint32_t g_playDelayEditSec = 0;
static int g_playDelayEditField = 2;  // 0 = hours, 1 = minutes, 2 = seconds (editor opens on seconds)
static uint32_t g_playDelayEditIgnoreUntilMs = 0;
struct PlayDelayEditKeys {
  bool bracketUpPrev;
  bool bracketDownPrev;
  bool semiHeldPrev;
  bool dotHeldPrev;
  bool enterPrev;
  bool cPrev;
  bool tabPrev;
  bool baselinesSynced;
};
static PlayDelayEditKeys g_pde{};
static bool g_trackNavAwaitRelease = false;
static bool g_trackNavPrevN = false;
static bool g_trackNavPrevB = false;
// Video loop side-channel: +1 next, -1 prev, 0 none.
static int g_videoTrackNavRequest = 0;
// MJPEG seek: rising edges for ,/</ vs /? — a ghost '/' can stay isKeyPressed() so "comma && !slash"
// never holds after the first seek-back; edges still catch each new comma tap.
static bool g_seekCommaPrevHeld = false;
static bool g_seekSlashPrevHeld = false;
// Separate baseline for video-only raw ,/</ vs /? edges (pollPlaybackKeys can miss under JPEG load).
static bool g_videoSeekRawPrevComma = false;
static bool g_videoSeekRawPrevSlash = false;
static bool g_playbackPollSPrev = false;
static bool g_playbackPollHPrev = false;
static bool g_mp3PollSPrev = false;
static bool g_mp3PollHPrev = false;

// HUD “bookmark”: updated when S marks during playback, or when S starts play from browser (countdown path).
static String g_sSetMediaPath;

// Browser pre-play: countdown in HUD list screen; Tab/Esc cancels. (Replaces fullscreen runPlayStartCountdown.)
static bool g_browserPreplayActive = false;
static bool s_browserPreplayHPrev = false;
// After S restarts preplay or starts countdown, ignore repeat pressEvents until S reads released (ghost FIFO).
static bool g_browserPreplayNeedSReleaseToRestart = false;
static uint32_t g_browserPreplayRemainSec = 0;
// For incremental list paint (avoids re-wiping the HUD panel every cursor step — main flicker source).
static int g_browserListPaintedSel = -1;
static int g_browserListPaintedScroll = -1;
static uint32_t g_browserPreplayNextTickMs = 0;
// Preplay cancel: require this many consecutive polls with no Tab before Tab is honored (clears hid/st.tab
// ghosts). Incremented only while !browserPreplayUserCancelHeldNow().
static uint8_t g_browserPreplayCancelQuietStreak = 0;
static String g_browserPreplayPath;
// After leaving playback (Tab/Esc/finish) restore browser cursor to the file that was being played.
static bool g_browserSelectPlayedMediaOnNextList = false;
// Some keyboard transitions (especially Tab exit from MP3) can confuse pressEvents/rising-edge.
// This flag arms the next completed S-hold to trigger timer-play after Tab/playback return.
static bool g_browserTimerPlayForceNextSDown = false;
// Similar one-shot for HUD toggle (C) after Tab-exit / playback return.
static bool g_browserHudForceNextCDown = false;
// Debug: show that markPlaybackReturnedToMenu() ran.
static bool g_debugShowTabExit = false;

static bool tabKeyHeldPhysical() {
  // Some firmware builds can report Tab with slightly different matrix coordinates.
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if ((p.x == 0 && p.y == 1) || (p.x == 1 && p.y == 1)) {
      return true;
    }
  }
  return false;
}

static bool tabEscHeldNow(const Keyboard_Class::KeysState &st) {
  return st.tab || hidHas(st.hid_keys, HID_ESC) || tabKeyHeldPhysical();
}

// Preplay cancel: do NOT use hid_keys (USB 0x29 ghosts and cancels countdown ~100–300ms after every S).
// Matrix Tab only — st.tab often stays true after Tab-exit and would block the quiet streak or read as held.
static bool browserPreplayUserCancelHeldNow(const Keyboard_Class::KeysState &st) {
  (void)st;
  return tabKeyHeldPhysical();
}

// Unified N/B track navigation detector (shared by MP3 + video paths).
// Guarantees one physical press => one track step, requiring release before next step.
static PlayKey pollTrackNavNextPrev() {
  static uint32_t trackNavLatchedAtMs = 0;
  static constexpr uint32_t kTrackNavLatchMaxMs = 900u;
  bool nHeld = false;
  bool bHeld = false;
  // Prefer keyList-based held detection; `isKeyPressed()` can ghost-stay after Tab transitions.
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (!nHeld && (kch == static_cast<uint8_t>('n') || kch == static_cast<uint8_t>('N') ||
                    kv.value_first == 'n' || kv.value_second == 'N')) {
      nHeld = true;
    }
    if (!bHeld && (kch == static_cast<uint8_t>('b') || kch == static_cast<uint8_t>('B') ||
                    kv.value_first == 'b' || kv.value_second == 'B')) {
      bHeld = true;
    }
    if (nHeld && bHeld) {
      break;
    }
  }

  bool nEdge = false;
  bool bEdge = false;
  int lastDir = 0;  // +1 next, -1 prev

  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (kch == static_cast<uint8_t>('n') || kch == static_cast<uint8_t>('N') ||
        kv.value_first == 'n' || kv.value_second == 'N') {
      nEdge = true;
      lastDir = +1;
    }
    if (kch == static_cast<uint8_t>('b') || kch == static_cast<uint8_t>('B') ||
        kv.value_first == 'b' || kv.value_second == 'B') {
      bEdge = true;
      lastDir = -1;
    }
  }

  // No held-state fallback for edges: relying on `pressEvents()` prevents
  // repeated steps when key hold state flickers (ghost-stuck after Tab exits).

  const uint32_t now = millis();
  static uint32_t trackNavReleaseQuietStartMs = 0u;
  constexpr uint32_t kTrackNavReleaseQuietMs = 90u;
  if (!nHeld && !bHeld) {
    if (trackNavReleaseQuietStartMs == 0u) {
      trackNavReleaseQuietStartMs = now;
    }
    // Only clear the latch after we have a stable release.
    if (g_trackNavAwaitRelease && (now - trackNavReleaseQuietStartMs) >= kTrackNavReleaseQuietMs) {
      g_trackNavAwaitRelease = false;
    }
  } else {
    trackNavReleaseQuietStartMs = 0u;
  }
  if (g_trackNavAwaitRelease && (now - trackNavLatchedAtMs) > kTrackNavLatchMaxMs && !nHeld &&
      !bHeld) {
    // Safety unlock only if we actually observed release.
    g_trackNavAwaitRelease = false;
    trackNavReleaseQuietStartMs = 0u;
  }
  if (g_trackNavAwaitRelease) {
    return PlayKey::NONE;
  }

  if (nEdge && !bEdge) {
    g_trackNavAwaitRelease = true;
    trackNavLatchedAtMs = now;
    return PlayKey::TRACK_NEXT;
  }
  if (bEdge && !nEdge) {
    g_trackNavAwaitRelease = true;
    trackNavLatchedAtMs = now;
    return PlayKey::TRACK_PREV;
  }
  if (nEdge && bEdge) {
    g_trackNavAwaitRelease = true;
    trackNavLatchedAtMs = now;
    return (lastDir >= 0) ? PlayKey::TRACK_NEXT : PlayKey::TRACK_PREV;
  }
  return PlayKey::NONE;
}

static bool tabEscBackRequested(const Keyboard_Class::KeysState &st) {
  if (tabEscHeldNow(st)) {
    return true;
  }
  for (char c : st.word) {
    if (c == 27 || c == '\t') {
      return true;
    }
  }
  return false;
}

static bool tabEscBackHeldOnly(const Keyboard_Class::KeysState &st) {
  // Playback path must be strict to avoid false BACK triggers from noisy matrix cells.
  return st.tab || hidHas(st.hid_keys, HID_ESC);
}

static bool playbackBackEdge(const Keyboard_Class::KeysState &st, bool &backArmed, bool &backPrevHeld,
                             uint32_t playbackStartMs) {
  const bool backHeld = tabEscBackHeldOnly(st);
  if (!backArmed) {
    // Rearm once key is released, or after startup guard timeout.
    if (!backHeld || (millis() - playbackStartMs) >= 450u) {
      backArmed = true;
    }
  }
  const bool backPressed = backArmed && backHeld && !backPrevHeld;
  backPrevHeld = backHeld;
  return backPressed;
}

static bool enterHeldNow(const Keyboard_Class::KeysState &st) {
  if (st.enter) {
    return true;
  }
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.x == 13 && p.y == 2) {
      return true;
    }
  }
  return false;
}

static bool enterPressedEdgeNow() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if (p.x == 13 && p.y == 2) {
      return true;
    }
  }
  return false;
}

// isKeyPressed + pressEvents (TCA8418) so s/S and c/C register reliably in the browser.
static bool menuLetterDownWithFifo(char lo, char hi) {
  if (M5Cardputer.Keyboard.isKeyPressed(lo) || M5Cardputer.Keyboard.isKeyPressed(hi)) {
    return true;
  }
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (kch == static_cast<uint8_t>(lo) || kch == static_cast<uint8_t>(hi)) {
      return true;
    }
    if (kv.value_first == lo || kv.value_first == hi || kv.value_second == lo || kv.value_second == hi) {
      return true;
    }
  }
  return false;
}

// Decode S/s from a matrix cell (same rules as fifo scan) for timer-play after MP3 when isKeyPressed lags.
static bool browserMenuKeyMeansS(uint8_t kch, const KeyValue_t &kv) {
  if (kch == static_cast<uint8_t>('s') || kch == static_cast<uint8_t>('S')) {
    return true;
  }
  return kv.value_first == 's' || kv.value_second == 's' || kv.value_first == 'S' ||
         kv.value_second == 'S';
}

static bool browserMenuKeyMeansC(uint8_t kch, const KeyValue_t &kv) {
  if (kch == static_cast<uint8_t>('c') || kch == static_cast<uint8_t>('C')) {
    return true;
  }
  return kv.value_first == 'c' || kv.value_second == 'c' || kv.value_first == 'C' ||
         kv.value_second == 'C';
}

// ADV: TCA8418KeyboardReader remaps to the same logical (x,y) grid as M5Cardputer Keyboard.h.
// S on row 2 → cell (3,2). After MP3/I2S teardown, isKeyPressed('s') can lie; matrix + pressEvents still work.
static bool browserMatrixCellIsTimerPlayS(const Point2D_t &p) {
  return p.x == 3 && p.y == 2;
}

// File list / FIFO: relaxed (7,2) when decode lags — ADV needs this or H never registers. Enter (13,2)
// is excluded; block hint when Enter is in the same buffer or keyList (see pollMenuKeys).

// Playback only: never treat (7,2) as H without a real h/H decode — Enter/matrix noise can ghost row-2 cells.
static bool browserHintHKeyStrictAtPoint(const Point2D_t &p) {
  if (p.y != 2 || p.x < 2 || p.x > 12 || p.x == 13) {
    return false;
  }
  const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
  const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
  if (kch == static_cast<uint8_t>('h') || kch == static_cast<uint8_t>('H')) {
    return true;
  }
  return kv.value_first == 'h' || kv.value_second == 'h' || kv.value_first == 'H' ||
         kv.value_second == 'H';
}

static bool browserMatrixCellIsKeysHintH(const Point2D_t &p) {
  return p.x == 7 && p.y == 2;
}

// Browser list / preplay: h/H decode or primary H cell (7,2) when decode lags — never Enter (13,2).
static bool browserHintHKeyAtPoint(const Point2D_t &p) {
  if (p.x == 13 && p.y == 2) {
    return false;
  }
  const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
  const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
  if (kch == static_cast<uint8_t>('h') || kch == static_cast<uint8_t>('H')) {
    return true;
  }
  if (kv.value_first == 'h' || kv.value_second == 'h' || kv.value_first == 'H' ||
      kv.value_second == 'H') {
    return true;
  }
  return browserMatrixCellIsKeysHintH(p);
}

static bool browserHintHMatrixHeldNow() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserHintHKeyAtPoint(p)) {
      return true;
    }
  }
  return false;
}

static bool browserPressEventsHaveDecodedHNotEnter() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if (browserHintHKeyAtPoint(p)) {
      return true;
    }
  }
  return false;
}

static bool browserHintHMatrixHeldStrictNow() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserHintHKeyStrictAtPoint(p)) {
      return true;
    }
  }
  return false;
}

static bool playbackKeysHintHHeldStrictNow() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if (browserHintHKeyStrictAtPoint(p)) {
      return true;
    }
  }
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserHintHKeyStrictAtPoint(p)) {
      return true;
    }
  }
  return false;
}

static void syncPlaybackKeysHintPollPrevAfterKeyboardUpdate() {
  const bool hHeld = playbackKeysHintHHeldStrictNow();
  g_playbackPollHPrev = hHeld;
  g_mp3PollHPrev = hHeld;
}

static bool browserTimerPlaySHeldNow() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserMatrixCellIsTimerPlayS(p)) {
      return true;
    }
    const uint8_t km = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kvm = M5Cardputer.Keyboard.getKeyValue(p);
    if (browserMenuKeyMeansS(km, kvm)) {
      return true;
    }
  }
  return M5Cardputer.Keyboard.isKeyPressed('s') || M5Cardputer.Keyboard.isKeyPressed('S');
}

// Cardputer ADV: M5 Speaker + ES8311 path needs heap for I2S + spk_task; re-init after MP3 I2S teardown.
static bool restoreCardputerSpeakerAfterMp3(int vol) {
  M5Cardputer.Speaker.end();
  delay(100);
  bool ok = M5Cardputer.Speaker.begin();
  if (!ok) {
    delay(150);
    M5Cardputer.Speaker.end();
    delay(100);
    ok = M5Cardputer.Speaker.begin();
  }
  if (ok) {
    M5Cardputer.Speaker.setVolume(vol);
  }
  return ok;
}

// Wraps I2S output so we can read approximate level for the MP3 visualizer.
class AudioOutputMeterI2S : public AudioOutputI2S {
public:
  explicit AudioOutputMeterI2S(int port = SPK_I2S_PORT) : AudioOutputI2S(port) {}

  volatile uint32_t visEnvelope = 0;

#if defined(ESP32)
  // Verbatim ESP8266Audio AudioOutputI2S::begin() ESP32 path except: (1) I2S_NUM_AUTO → SPK_I2S_PORT
  // so the second session matches M5 ADV (I2S1, pins 41/43/42); (2) no assert() → return false / del_channel.
  bool begin() override {
    if (i2sOn) {
      return true;
    }
    i2s_chan_config_t chan_cfg =
        I2S_CHANNEL_DEFAULT_CONFIG(static_cast<i2s_port_t>(SPK_I2S_PORT), I2S_ROLE_MASTER);
    chan_cfg.dma_desc_num = _buffers;
    chan_cfg.dma_frame_num = _bufferWords;
    if (i2s_new_channel(&chan_cfg, &_tx_handle, nullptr) != ESP_OK) {
      return false;
    }

    i2s_std_config_t std_cfg = {
        .clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(hertz),
        .slot_cfg = I2S_STD_MSB_SLOT_DEFAULT_CONFIG(I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_STEREO),
        .gpio_cfg = {
            .mclk = mclkPin < 0 ? I2S_GPIO_UNUSED : (gpio_num_t)mclkPin,
            .bclk = bclkPin < 0 ? I2S_GPIO_UNUSED : (gpio_num_t)bclkPin,
            .ws = wclkPin < 0 ? I2S_GPIO_UNUSED : (gpio_num_t)wclkPin,
            .dout = (gpio_num_t)doutPin,
            .din = I2S_GPIO_UNUSED,
            .invert_flags = {
                .mclk_inv = false,
                .bclk_inv = false,
                .ws_inv = false,
            },
        },
    };
#if SOC_CLK_APLL_SUPPORTED
    std_cfg.clk_cfg.clk_src = _useAPLL ? i2s_clock_src_t::I2S_CLK_SRC_APLL : i2s_clock_src_t::I2S_CLK_SRC_DEFAULT;
#endif
    std_cfg.slot_cfg.bit_shift = !lsb_justified; // I2S = shift, LSBJ = no shift
    if (i2s_channel_init_std_mode(_tx_handle, &std_cfg) != ESP_OK) {
      i2s_del_channel(_tx_handle);
      _tx_handle = nullptr;
      return false;
    }

    int16_t a[2] = {0, 0};
    size_t written = 0;
    do {
      i2s_channel_preload_data(_tx_handle, (void *)a, sizeof(a), &written);
    } while (written);

    i2sOn = (ESP_OK == i2s_channel_enable(_tx_handle));
    SetRate(hertz ? hertz : 44100);
    return true;
  }
#endif

  bool ConsumeSample(int16_t sample[2]) override {
    const int a = sample[0] > 0 ? sample[0] : -sample[0];
    const int b = sample[1] > 0 ? sample[1] : -sample[1];
    const uint32_t pk = static_cast<uint32_t>(a > b ? a : b);
    uint32_t e = visEnvelope;
    if (pk > e) {
      e = pk;
    } else {
      e = (e * 15 + pk) / 16;
    }
    visEnvelope = e;
    return AudioOutputI2S::ConsumeSample(sample);
  }
};

static bool initSd() {
  SPI.begin(SD_SPI_SCK_PIN, SD_SPI_MISO_PIN, SD_SPI_MOSI_PIN, SD_SPI_CS_PIN);
  if (!SD.begin(SD_SPI_CS_PIN, SPI, 25000000)) {
    Serial.println("SD init failed");
    return false;
  }
  if (SD.cardType() == CARD_NONE) {
    Serial.println("No SD card");
    return false;
  }
  return true;
}

static bool isMjpegFileName(const String &baseName) {
  return baseName.endsWith(".mjpeg") || baseName.endsWith(".MJPEG") ||
         baseName.endsWith(".mjpg") || baseName.endsWith(".MJPG");
}

static bool isMp3FileName(const String &baseName) {
  return baseName.endsWith(".mp3") || baseName.endsWith(".MP3");
}

static String pcmPathForMjpeg(const String &mjpegPath) {
  String base = mjpegPath;
  const char *exts[] = {".mjpeg", ".MJPEG", ".mjpg", ".MJPG"};
  for (const char *e : exts) {
    if (base.endsWith(e)) {
      base = base.substring(0, base.length() - static_cast<int>(strlen(e)));
      break;
    }
  }
  return base + ".pcm";
}

static String displayBasename(const String &path) {
  String p = path;
  if (p.startsWith("/")) {
    p = p.substring(1);
  }
  int slash = p.lastIndexOf('/');
  if (slash >= 0) {
    p = p.substring(slash + 1);
  }
  return p;
}

static String pathJoin(const String &dir, const String &name) {
  if (name.length() == 0) {
    return dir;
  }
  if (dir == "/") {
    return "/" + name;
  }
  if (dir.endsWith("/")) {
    return dir + name;
  }
  return dir + "/" + name;
}

static String pathParent(const String &dir) {
  if (dir.length() <= 1 || dir == "/") {
    return "/";
  }
  String s = dir;
  while (s.length() > 1 && s.endsWith("/")) {
    s.remove(s.length() - 1);
  }
  const int i = s.lastIndexOf('/');
  if (i <= 0) {
    return "/";
  }
  return s.substring(0, i);
}

// Last path segment from SD file name (may be "file.mp3" or "Music/file.mp3")
static String sdEntryBaseName(const char *raw) {
  String s = raw;
  if (s.startsWith("/")) {
    s = s.substring(1);
  }
  const int i = s.lastIndexOf('/');
  if (i >= 0) {
    s = s.substring(i + 1);
  }
  return s;
}

static void listMediaDir(const String &cwdIn, std::vector<MediaEntry> &out) {
  out.clear();
  String cwd = cwdIn.length() ? cwdIn : "/";

  if (cwd != "/") {
    MediaEntry up;
    up.label = "..";
    up.fullPath = pathParent(cwd);
    up.isDir = true;
    out.push_back(up);
  }

  std::vector<MediaEntry> dirs;
  std::vector<MediaEntry> files;

  File d = SD.open(cwd.c_str());
  if (!d || !d.isDirectory()) {
    if (d) {
      d.close();
    }
    return;
  }
  for (;;) {
    File f = d.openNextFile();
    if (!f) {
      break;
    }
    const String base = sdEntryBaseName(f.name());
    if (base.length() == 0 || base == "." || base == "..") {
      f.close();
      continue;
    }
    const String full = pathJoin(cwd, base);
    if (f.isDirectory()) {
      MediaEntry e;
      e.label = base;
      e.fullPath = full;
      e.isDir = true;
      dirs.push_back(e);
    } else if (isMjpegFileName(base) || isMp3FileName(base)) {
      MediaEntry e;
      e.label = base;
      e.fullPath = full;
      e.isDir = false;
      files.push_back(e);
    }
    f.close();
  }
  d.close();

  auto byLabel = [](const MediaEntry &a, const MediaEntry &b) {
    return strcasecmp(a.label.c_str(), b.label.c_str()) < 0;
  };
  std::sort(dirs.begin(), dirs.end(), byLabel);
  std::sort(files.begin(), files.end(), byLabel);
  for (auto &e : dirs) {
    out.push_back(e);
  }
  for (auto &e : files) {
    out.push_back(e);
  }
}

// Next playable file after `finishedPath` in its parent folder (same order as browser file list).
static bool getNextMediaInFolder(const String &finishedPath, bool wrapFolder, String &outNext) {
  const String dir = pathParent(finishedPath);
  std::vector<MediaEntry> list;
  listMediaDir(dir, list);
  std::vector<String> files;
  for (const auto &e : list) {
    if (!e.isDir) {
      files.push_back(e.fullPath);
    }
  }
  if (files.empty()) {
    return false;
  }
  int idx = -1;
  for (size_t i = 0; i < files.size(); i++) {
    if (files[i] == finishedPath) {
      idx = static_cast<int>(i);
      break;
    }
  }
  if (idx < 0) {
    return false;
  }
  int nxt = idx + 1;
  if (nxt >= static_cast<int>(files.size())) {
    if (!wrapFolder) {
      return false;
    }
    nxt = 0;
  }
  outNext = files[static_cast<size_t>(nxt)];
  return true;
}

// Previous playable file before `currentPath` in its parent folder (same order as browser).
static bool getPrevMediaInFolder(const String &currentPath, bool wrapFolder, String &outPrev) {
  const String dir = pathParent(currentPath);
  std::vector<MediaEntry> list;
  listMediaDir(dir, list);
  std::vector<String> files;
  for (const auto &e : list) {
    if (!e.isDir) {
      files.push_back(e.fullPath);
    }
  }
  if (files.empty()) {
    return false;
  }
  int idx = -1;
  for (size_t i = 0; i < files.size(); i++) {
    if (files[i] == currentPath) {
      idx = static_cast<int>(i);
      break;
    }
  }
  if (idx < 0) {
    return false;
  }
  int prv = idx - 1;
  if (prv < 0) {
    if (!wrapFolder) {
      return false;
    }
    prv = static_cast<int>(files.size()) - 1;
  }
  outPrev = files[static_cast<size_t>(prv)];
  return true;
}

static bool hidHas(const std::vector<uint8_t> &hid, uint8_t code) {
  for (uint8_t h : hid) {
    if (h == code) {
      return true;
    }
  }
  return false;
}

// S=timer-play must not consult `st.tab`: it can stay true after Tab cancels preplay while the key is
// already up, which blocked every later S until the soft state cleared.
static bool browserPhysicalTabOrUsbEscHeld(const Keyboard_Class::KeysState &st) {
  return tabKeyHeldPhysical() || hidHas(st.hid_keys, HID_ESC);
}

static bool browserTabOrEscBlocksTimerPlayS(const Keyboard_Class::KeysState &st) {
  // Do not gate timer-play S on st.hid_keys / HID_ESC: on Cardputer ADV the internal Tab↔Esc path often
  // leaves usage 0x29 visible in hid_keys even when no key is down, which made every S poll a no-op.
  // Tab long-press timer-play and up-dir still use tabEscHeldNow / matrix elsewhere.
  (void)st;
  return false;
}

// Caller must run M5Cardputer.update() and Keyboard.updateKeysState() first (same frame).
static bool systemInfoKeysHeld() {
  // Physical coordinates are more reliable than char translation on this keyboard.
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if ((p.x == 10 && p.y == 0) || (p.x == 8 && p.y == 1)) {  // '0' or 'i'
      return true;
    }
  }
  return false;
}

static bool g_sysInfoOverlayVisible = false;
static uint32_t g_sysInfoLastToggleMs = 0;
static constexpr uint32_t kSysInfoToggleDebounceMs = 220u;

static bool systemInfoTogglePressedEdge() {
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if ((p.x == 10 && p.y == 0) || (p.x == 8 && p.y == 1)) {  // '0' or 'i'
      return true;
    }
  }
  return false;
}

// Press 0/i once to show system info; press again to hide.
static bool systemInfoOverlayActive() {
  const uint32_t now = millis();
  if (systemInfoTogglePressedEdge() &&
      (now - g_sysInfoLastToggleMs) >= kSysInfoToggleDebounceMs) {
    g_sysInfoLastToggleMs = now;
    g_sysInfoOverlayVisible = !g_sysInfoOverlayVisible;
  }
  return g_sysInfoOverlayVisible;
}

static void drawSystemInfoScreen() {
  static uint32_t s_lastRedrawMs = 0;
  static constexpr uint32_t kSysInfoRedrawIntervalMs = 260u;
  const uint32_t now = millis();
  if ((now - s_lastRedrawMs) < kSysInfoRedrawIntervalMs) {
    return;
  }
  s_lastRedrawMs = now;

  auto &d = M5Cardputer.Display;
  d.fillScreen(TFT_BLACK);
  d.setTextSize(1);
  d.setTextColor(TFT_CYAN, TFT_BLACK);
  d.drawString("System info (0/i toggle)", 4, 2);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  int y = 16;
  char line[44];

  const int32_t pct = M5Cardputer.Power.getBatteryLevel();
  if (pct >= 0 && pct <= 100) {
    snprintf(line, sizeof(line), "Battery: %ld%%", static_cast<long>(pct));
  } else {
    snprintf(line, sizeof(line), "Battery: n/a");
  }
  d.drawString(line, 4, y);
  y += 12;

  const int16_t batMv = M5Cardputer.Power.getBatteryVoltage();
  snprintf(line, sizeof(line), "Vbat: %d mV", static_cast<int>(batMv));
  d.drawString(line, 4, y);
  y += 12;

  const char *chg = "?";
  switch (M5Cardputer.Power.isCharging()) {
    case m5::Power_Class::is_charging:
      chg = "charging";
      break;
    case m5::Power_Class::is_discharging:
      chg = "discharging";
      break;
    default:
      chg = "unknown";
      break;
  }
  snprintf(line, sizeof(line), "State: %s", chg);
  d.drawString(line, 4, y);
  y += 12;

  const int16_t vbus = M5Cardputer.Power.getVBUSVoltage();
  if (vbus >= 0) {
    snprintf(line, sizeof(line), "VBUS: %d mV", static_cast<int>(vbus));
    d.drawString(line, 4, y);
    y += 12;
  }

  const int32_t ibat = M5Cardputer.Power.getBatteryCurrent();
  snprintf(line, sizeof(line), "Ibat: %ld mA", static_cast<long>(ibat));
  d.drawString(line, 4, y);
  y += 12;

#if defined(ESP_PLATFORM)
  snprintf(line, sizeof(line), "Heap: %u free", static_cast<unsigned>(ESP.getFreeHeap()));
  d.drawString(line, 4, y);
  y += 12;
  snprintf(line, sizeof(line), "CPU: %u MHz", static_cast<unsigned>(ESP.getCpuFreqMHz()));
  d.drawString(line, 4, y);
  y += 12;
#endif

  snprintf(line, sizeof(line), "Up: %lu s", static_cast<unsigned long>(millis() / 1000u));
  d.drawString(line, 4, y);
  y += 12;

  snprintf(line, sizeof(line), "Bright: %u", static_cast<unsigned>(d.getBrightness()));
  d.setTextColor(TFT_DARKGREY, TFT_BLACK);
  d.drawString(line, 4, y);
#if defined(ESP_PLATFORM)
  yield();
#endif
}

static void drawStartupSplashTextLines() {
  auto &d = M5Cardputer.Display;
  const int dw = d.width();
  const int dh = d.height();
  d.setTextSize(1);
  d.setTextColor(TFT_WHITE, 0x4D7B);
  d.drawCenterString("CardputerADV-BasicAV", dw / 2, dh - 32);
  d.setTextColor(TFT_CYAN, 0x4D7B);
  d.drawCenterString("v1.0", dw / 2, dh - 20);
  d.setTextColor(TFT_WHITE, 0x4D7B);
  d.drawCenterString("MJPEG / MP3", dw / 2, dh - 8);
}

// PNG IHDR width/height at bytes 16–23 (big-endian). Used so we can set explicit zoom + top_left — LGFX
// middle_center + auto fit (0,0 zoom) was clipping parts of some RGBA PNGs on Cardputer.
static bool splashReadPngIhdr(const uint8_t *data, size_t len, int32_t &outW, int32_t &outH) {
  if (len < 24) {
    return false;
  }
  if (data[0] != 0x89 || data[1] != 'P' || data[2] != 'N' || data[3] != 'G') {
    return false;
  }
  outW = (static_cast<int32_t>(data[16]) << 24) | (static_cast<int32_t>(data[17]) << 16) |
         (static_cast<int32_t>(data[18]) << 8) | static_cast<int32_t>(data[19]);
  outH = (static_cast<int32_t>(data[20]) << 24) | (static_cast<int32_t>(data[21]) << 16) |
         (static_cast<int32_t>(data[22]) << 8) | static_cast<int32_t>(data[23]);
  if (outW <= 0 || outH <= 0 || outW > 8192 || outH > 8192) {
    return false;
  }
  return true;
}

static bool splashReadPngIhdrFromFile(File &f, int32_t &outW, int32_t &outH) {
  uint8_t hdr[24];
  const size_t n = f.read(hdr, sizeof(hdr));
  (void)f.seek(0);
  if (n != sizeof(hdr)) {
    return false;
  }
  return splashReadPngIhdr(hdr, sizeof(hdr), outW, outH);
}

// Stretch splash toward dw×dh (separate zoom_x / zoom_y), then scale down slightly and center — no hard crop.
// kVisualFudge: <1 shrinks from full edge-to-edge (0.60 ≈ 40% smaller).
static void splashTapeStretchFillZooms(int dw, int dh, int32_t picW, int32_t picH, float &zoomX, float &zoomY,
                                       int &drawX, int &drawY) {
  static constexpr float kShrink = 0.9995f;
  static constexpr float kVisualFudge = 0.60f;
  const int32_t pw = std::max<int32_t>(1, picW);
  const int32_t ph = std::max<int32_t>(1, picH);
  zoomX = static_cast<float>(dw) / static_cast<float>(pw);
  zoomY = static_cast<float>(dh) / static_cast<float>(ph);
  for (int iter = 0; iter < 24; ++iter) {
    const int ow = static_cast<int>(ceilf(static_cast<float>(pw) * zoomX - 1e-4f));
    const int oh = static_cast<int>(ceilf(static_cast<float>(ph) * zoomY - 1e-4f));
    if (ow <= dw && oh <= dh) {
      break;
    }
    if (ow > dw) {
      zoomX *= static_cast<float>(dw) / static_cast<float>(std::max(1, ow)) * kShrink;
    }
    if (oh > dh) {
      zoomY *= static_cast<float>(dh) / static_cast<float>(std::max(1, oh)) * kShrink;
    }
  }
  zoomX *= kVisualFudge;
  zoomY *= kVisualFudge;
  const int outW = static_cast<int>(ceilf(static_cast<float>(pw) * zoomX - 1e-4f));
  const int outH = static_cast<int>(ceilf(static_cast<float>(ph) * zoomY - 1e-4f));
  drawX = (dw - std::min(outW, dw)) / 2;
  drawY = (dh - std::min(outH, dh)) / 2;
}

// MP3 tape still viz: keep PNG aspect ratio (uniform zoom) and center it in the viz band.
static void tapeAspectContainZooms(int dw, int dh, int32_t picW, int32_t picH, float &zoomX, float &zoomY,
                                    int &drawX, int &drawY) {
  // Keep aspect ratio (uniform zoom) while letting the image fill the band.
  // Match the splash inset sizing: splash helper uses ~0.60.
  static constexpr float kVisualFudge = 0.60f;
  const int32_t pw = std::max<int32_t>(1, picW);
  const int32_t ph = std::max<int32_t>(1, picH);
  const float zx = static_cast<float>(dw) / static_cast<float>(pw);
  const float zy = static_cast<float>(dh) / static_cast<float>(ph);
  const float zoom = std::min(zx, zy) * kVisualFudge;

  zoomX = zoom;
  zoomY = zoom;

  const int outW = static_cast<int>(ceilf(static_cast<float>(pw) * zoom - 1e-4f));
  const int outH = static_cast<int>(ceilf(static_cast<float>(ph) * zoom - 1e-4f));
  drawX = (dw - std::min(outW, dw)) / 2;
  drawY = (dh - std::min(outH, dh)) / 2;
}

// MP3 tape still: stretch to fill the entire viz band (may distort aspect ratio).
static void tapeStretchToFillZooms(int dw, int dh, int32_t picW, int32_t picH, float &zoomX, float &zoomY,
                                    int &drawX, int &drawY) {
  const int32_t pw = std::max<int32_t>(1, picW);
  const int32_t ph = std::max<int32_t>(1, picH);
  zoomX = static_cast<float>(dw) / static_cast<float>(pw);
  zoomY = static_cast<float>(dh) / static_cast<float>(ph);
  // Use top-left so the scaled image fills the clip rect.
  drawX = 0;
  drawY = 0;
}

// Splash: tape PNG from SD list — stretch + inset; captions on top (opaque bg on glyphs).
static void drawStartupSplashFrame(bool sdMounted) {
  auto &d = M5Cardputer.Display;
  const int dw = d.width();
  const int dh = d.height();
  // LGFX PNG sizing uses the current clip rect; a leftover sub-rect from UI shrinks maxWidth/maxHeight and clips art.
  d.setClipRect(0, 0, dw, dh);
  d.fillScreen(0x4D7B);
  bool drewPng = false;
  if (sdMounted) {
#if defined(ESP_PLATFORM)
    yield();
#endif
    for (size_t i = 0; i < kSplashImagePngPathCount; ++i) {
      const char *path = kSplashImagePngPaths[i];
      File sf = SD.open(path, FILE_READ);
      if (!sf) {
        continue;
      }
      int32_t picW = 0;
      int32_t picH = 0;
      if (!splashReadPngIhdrFromFile(sf, picW, picH)) {
        sf.close();
        continue;
      }
      sf.close();
      float zx = 1.0f;
      float zy = 1.0f;
      int sx = 0;
      int sy = 0;
      splashTapeStretchFillZooms(dw, dh, picW, picH, zx, zy, sx, sy);
      if (d.drawPngFile(SD, path, sx, sy, 0, 0, 0, 0, zx, zy, lgfx::datum_t::top_left)) {
        drewPng = true;
        break;
      }
    }
  }
  if (!drewPng) {
#if defined(ESP_PLATFORM)
    yield();
#endif
    int32_t picW = 0;
    int32_t picH = 0;
    if (splashReadPngIhdr(kTapeOMagneticSplashPng, kTapeOMagneticSplashPngLen, picW, picH)) {
      float zx = 1.0f;
      float zy = 1.0f;
      int sx = 0;
      int sy = 0;
      splashTapeStretchFillZooms(dw, dh, picW, picH, zx, zy, sx, sy);
      const uint32_t splashLen = static_cast<uint32_t>(kTapeOMagneticSplashPngLen);
      (void)d.drawPng(kTapeOMagneticSplashPng, splashLen, sx, sy, 0, 0, 0, 0, zx, zy,
                      lgfx::datum_t::top_left);
    }
  }
  d.setClipRect(0, 0, dw, dh);
  drawStartupSplashTextLines();
}

// Last unambiguous volume direction seen from pressEvents().
// -1 = down, +1 = up, 0 = unknown.
static int g_volLastDir = 0;
static bool g_volDownHeldPrev = false;
static bool g_volUpHeldPrev = false;

static void resetPlaybackKeyboardBaselines() {
  g_volDownHeldPrev = false;
  g_volUpHeldPrev = false;
  g_volLastDir = 0;
  g_trackNavPrevN = false;
  g_trackNavPrevB = false;
  g_trackNavAwaitRelease = false;
  g_seekCommaPrevHeld = false;
  g_seekSlashPrevHeld = false;
  g_videoSeekRawPrevComma = false;
  g_videoSeekRawPrevSlash = false;
  g_playbackPollSPrev = false;
  g_playbackPollHPrev = false;
  g_mp3PollSPrev = false;
  g_mp3PollHPrev = false;
}

static void markPlaybackReturnedToMenu() {
  resetPlaybackKeyboardBaselines();
  clearKeysHintForMedia();
  const uint32_t m = millis();
  g_menuSuppressTabEscUpDir = true;
  g_menuTabSuppressArmMs = m;
  g_menuLastEnterAtMs = m;
  g_menuSuppressEnterUntilRelease = true;
  g_menuSuppressEnterPlayback = true;
  g_menuSuppressEnterArmMs = m;
  g_menuSyncEnterEdgeOnNextPoll = true;
  g_menuResetListNavEdgesOnNextPoll = true;
  g_menuResetBrowserLetterTogglesOnNextPoll = true;
  g_menuSyncTabEscBackBaselineOnNextPoll = true;
  g_browserListPaintedSel = -1;
  g_browserListPaintedScroll = -1;
  g_browserTimerPlayLastMs = 0;
  // H baseline: g_menuResetBrowserLetterTogglesOnNextPoll arms s_browserHintResyncHBaselineNextPoll
  // so the next pollMenuKeys snaps prev/FIFO to post-I2S matrix state (do not zero prev here).
  // Next browser list paint: select the media that was played so S always re-triggers.
  g_browserSelectPlayedMediaOnNextList = true;
  // Do not set g_browserTimerPlayForceNextSDown here: keyChanged + sKeyCellNow/sHeldAny after MP3/Tab
  // was firing TIMER_PLAY_FILE once on the list without touching S (auto countdown).
  // Force stays for preplay Tab-cancel / edge cases only; S uses FIFO + rise/press/driver edges.
  // Force the next C-down in browser to toggle HUD even if edge/FIFO confuse.
  g_browserHudForceNextCDown = true;
  g_debugShowTabExit = true;
  // Matrix often still reads Tab down after Tab-exit; sync wasDown so the list does not see a fake Tab-down.
  M5Cardputer.update();
  M5Cardputer.Keyboard.updateKeysState();
  s_menuTabWasDown = tabKeyHeldPhysical();
}

static void markMenuSettleAfterModal() {
  g_menuSuppressTabEscUpDir = true;
  g_menuTabSuppressArmMs = millis();
  g_menuSuppressEnterUntilRelease = true;
  g_menuSuppressEnterPlayback = false;
  g_menuSuppressEnterArmMs = millis();
  g_menuResetListNavEdgesOnNextPoll = true;
}

static void showVolumeHintNow() {
  // Each press restarts the timer so rapid clicks keep the OSD alive; long enough to read final %.
  g_mp3VolHintUntil = millis() + 2600u;
  g_mp3VolHintActive = true;
}

static bool keyValueMeansVolDown(const KeyValue_t &kv) {
  return kv.value_first == '-' || kv.value_first == '_' || kv.value_second == '_';
}

static bool keyValueMeansVolUp(const KeyValue_t &kv) {
  return kv.value_first == '=' || kv.value_first == '+' || kv.value_second == '+';
}

static bool byteMeansVolDown(uint8_t kch) {
  return kch == static_cast<uint8_t>('-') || kch == static_cast<uint8_t>('_');
}

static bool byteMeansVolUp(uint8_t kch) {
  return kch == static_cast<uint8_t>('=') || kch == static_cast<uint8_t>('+');
}

// Fallback if coordinates differ from stock map (optional; logical key scan usually wins).
static bool volMatrixCellIsDown(const Point2D_t &p) {
  if (kVolumeMinusPlusMatrixColsSwapped) {
    return p.x == 11 && p.y == 0;
  }
  return p.x == 10 && p.y == 0;
}

static bool volMatrixCellIsUp(const Point2D_t &p) {
  if (kVolumeMinusPlusMatrixColsSwapped) {
    return p.x == 10 && p.y == 0;
  }
  return p.x == 11 && p.y == 0;
}

// True only for real volume keys — comma/slash can share row 0 matrix coords; coords alone blocked seek.
static bool playbackVolumeKeysHeldNow() {
  if (M5Cardputer.Keyboard.isKeyPressed('-') || M5Cardputer.Keyboard.isKeyPressed('_') ||
      M5Cardputer.Keyboard.isKeyPressed('=') || M5Cardputer.Keyboard.isKeyPressed('+')) {
    return true;
  }
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (volMatrixCellIsDown(p) &&
        (byteMeansVolDown(kch) || keyValueMeansVolDown(kv))) {
      return true;
    }
    if (volMatrixCellIsUp(p) &&
        (byteMeansVolUp(kch) || keyValueMeansVolUp(kv))) {
      return true;
    }
  }
  return false;
}

// Volume: `-` / `_` lower; `=` / `+` raise. ADV (TCA8418) can report keys where getKeyValue() at the
// coordinate does not match the shifted character — use getKey(p) + keysState.word + matrix cells.
static void pollVolumeKeysMatrix(AudioOutputI2S *applyGainTo) {
  const bool heldDownChars = M5Cardputer.Keyboard.isKeyPressed('-') ||
                             M5Cardputer.Keyboard.isKeyPressed('_');
  const bool heldUpChars =
      M5Cardputer.Keyboard.isKeyPressed('=') || M5Cardputer.Keyboard.isKeyPressed('+');
  bool matrixDownNow = false;
  bool matrixUpNow = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    const uint8_t kchM = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kvM = M5Cardputer.Keyboard.getKeyValue(p);
    if (volMatrixCellIsDown(p) &&
        (byteMeansVolDown(kchM) || keyValueMeansVolDown(kvM))) {
      matrixDownNow = true;
    }
    if (volMatrixCellIsUp(p) &&
        (byteMeansVolUp(kchM) || keyValueMeansVolUp(kvM))) {
      matrixUpNow = true;
    }
  }
  const bool volDownNow = heldDownChars || matrixDownNow;
  const bool volUpNow = heldUpChars || matrixUpNow;

  const int d = kSpeakerVolumeStep;
  bool peDown = false;
  bool peUp = false;
  // Use pressEvents iteration order as time proxy (TCA8418 FIFO drain).
  int peLastDir = 0;
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    int evDir = 0;  // -1 down, +1 up
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (byteMeansVolDown(kch)) {
      evDir = -1;
    } else if (byteMeansVolUp(kch)) {
      evDir = +1;
    }
    if (evDir == 0) {
      if (keyValueMeansVolDown(kv)) {
        evDir = -1;
      } else if (keyValueMeansVolUp(kv)) {
        evDir = +1;
      }
    }
    // No coordinate-only fallback: `,`/`/` can share row 0 with `-`/`=`; that miscounted as volume,
    // set g_lastVolumeStepMs, and suppressed comma seek after the first successful seek-back.
    if (evDir < 0) {
      peDown = true;
      peLastDir = -1;
    } else if (evDir > 0) {
      peUp = true;
      peLastDir = +1;
    }
  }

  if (!peDown && !peUp) {
    // Recovery path: if pressEvents temporarily stall, still step on held-state edges.
    const bool downEdge = volDownNow && !g_volDownHeldPrev;
    const bool upEdge = volUpNow && !g_volUpHeldPrev;
    g_volDownHeldPrev = volDownNow;
    g_volUpHeldPrev = volUpNow;
    if (!downEdge && !upEdge) {
      return;
    }
    int dir = 0;
    if (downEdge && !upEdge) {
      dir = -1;
    } else if (!downEdge && upEdge) {
      dir = +1;
    } else if (heldUpChars && !heldDownChars) {
      dir = +1;
    } else if (heldDownChars && !heldUpChars) {
      dir = -1;
    } else if (g_volLastDir != 0) {
      dir = g_volLastDir;
    } else {
      dir = -1;
    }
    int v = g_speakerVolumePersist;
    if (dir < 0) {
      v -= d;
    } else if (dir > 0) {
      v += d;
    }
    setSpeakerVolumePersisted(constrain(v, 0, 255));
    g_lastVolumeStepMs = millis();
    showVolumeHintNow();
    if (applyGainTo) {
      applyI2sGainFromSpeakerVolume(applyGainTo);
    }
    return;
  }

  // Exactly one step per press-edge.
  int dir = 0;
  if (peDown && !peUp) {
    dir = -1;
  } else if (!peDown && peUp) {
    dir = +1;
  } else if (peLastDir != 0) {
    dir = peLastDir;
  } else if (g_volLastDir != 0) {
    dir = g_volLastDir;
  } else {
    dir = -1;
  }

  if (peDown && !peUp) {
    g_volLastDir = -1;
  } else if (!peDown && peUp) {
    g_volLastDir = +1;
  } else if (peLastDir != 0) {
    g_volLastDir = peLastDir;
  }
  g_volDownHeldPrev = volDownNow;
  g_volUpHeldPrev = volUpNow;

  int v = g_speakerVolumePersist;
  if (dir < 0) {
    v -= d;
  } else if (dir > 0) {
    v += d;
  }
  setSpeakerVolumePersisted(constrain(v, 0, 255));
  g_lastVolumeStepMs = millis();
  showVolumeHintNow();
  g_ignorePauseToggleUntilMs = millis() + 120u;
  if (applyGainTo) {
    applyI2sGainFromSpeakerVolume(applyGainTo);
  }
}

static void applyI2sGainFromSpeakerVolume(AudioOutputI2S *out) {
  if (!out) {
    return;
  }
  const int v = g_speakerVolumePersist;
  // Cap gain below 3.5 to reduce clipping on loud MP3s; larger I2S DMA helps underrun crackle.
  const float g = constrain(v / 255.0f * 1.9f, 0.05f, 2.4f);
  out->SetGain(g);
}

// Optional short clip from SD during splash (same I2S handoff as full MP3 playback).
static void playSplashJingleFromSdIfPresent() {
  if (!SD.exists(kSplashJinglePath)) {
    delay(1600);
    return;
  }
  const int vol = g_speakerVolumePersist;
  M5Cardputer.Speaker.stop();
  M5Cardputer.Speaker.end();
  delay(90);

  auto *out = new AudioOutputMeterI2S(SPK_I2S_PORT);
  auto *file = new AudioFileSourceSD();
  auto *mp3 = new AudioGeneratorMP3();
  if (!out || !file || !mp3) {
    delete mp3;
    delete file;
    delete out;
    restoreCardputerSpeakerAfterMp3(vol);
    delay(1600);
    return;
  }
  out->SetPinout(SPK_PIN_BCLK, SPK_PIN_LRCLK, SPK_PIN_DOUT);
  out->SetOutputModeMono(true);
#if defined(ESP32)
  out->SetBuffers(12, 2304);
#endif
  applyI2sGainFromSpeakerVolume(out);

  if (!file->open(kSplashJinglePath) || !mp3->begin(file, out)) {
    mp3->stop();
    file->close();
    delete mp3;
    delete file;
    out->stop();
    delay(40);
    delete out;
    restoreCardputerSpeakerAfterMp3(vol);
    delay(1600);
    return;
  }

  const uint32_t jingleStarted = millis();
  while (mp3->isRunning()) {
    if (millis() - jingleStarted > kSplashJingleMaxMs) {
      break;
    }
    if (!mp3->loop()) {
      break;
    }
    yield();
    delay(1);
  }
  mp3->stop();
  file->close();
  delete mp3;
  delete file;
  out->stop();
  delay(40);
  delete out;
  restoreCardputerSpeakerAfterMp3(vol);
}

static bool skipOneJpegFrame(File &v) {
  while (v.available()) {
    if (g_mjpeg.readMjpegBuf()) {
      return true;
    }
  }
  return false;
}

static bool jumpToVideoFrame(const String &videoPath, const String &pcmPath, File &v, File &pcm,
                             bool &pcmOpen, int &nextFrameIdx) {
  M5Cardputer.Speaker.stop();
  g_mjpeg.reset();
  v.close();
  if (pcmOpen) {
    pcm.close();
    pcmOpen = false;
  }

  v = SD.open(videoPath.c_str(), FILE_READ);
  if (!v || v.isDirectory()) {
    return false;
  }
  g_mjpeg.setup(v, g_mjpegBuf, &M5Cardputer.Display, false);

  const int wantSkip = nextFrameIdx;
  int done = 0;
  for (int i = 0; i < wantSkip; i++) {
    if (!skipOneJpegFrame(v)) {
      break;
    }
    done++;
  }
  // Keep index aligned with how many JPEGs we actually skipped (EOF / short file used to return
  // false here and abort playback, so backward seek looked like it did nothing).
  nextFrameIdx = done;

  if (SD.exists(pcmPath.c_str())) {
    pcm = SD.open(pcmPath.c_str(), FILE_READ);
    if (pcm && !pcm.isDirectory() && pcm.size() > 0) {
      pcmOpen = true;
      const size_t off = static_cast<size_t>(nextFrameIdx) * AUDIO_CHUNK;
      if (off < pcm.size()) {
        pcm.seek(off);
      } else {
        pcm.seek(pcm.size());
      }
    } else {
      if (pcm) {
        pcm.close();
      }
    }
  }
  return true;
}

static void formatHms24(uint32_t sec, char *buf, size_t len) {
  const uint32_t h = sec / 3600u;
  const uint32_t m = (sec % 3600u) / 60u;
  const uint32_t s = sec % 60u;
  snprintf(buf, len, "%02u:%02u:%02u", h, m, s);
}

static uint32_t clampPlayStartDelaySec(uint32_t sec) {
  return sec > kPlayStartDelayMaxSec ? kPlayStartDelayMaxSec : sec;
}

// field 0 = hours, 1 = minutes, 2 = seconds.
static void playDelayAdjustField(uint32_t &sec, int field, int delta) {
  int64_t t = static_cast<int64_t>(sec);
  if (field == 0) {
    t += static_cast<int64_t>(delta) * 3600;
  } else if (field == 1) {
    t += static_cast<int64_t>(delta) * 60;
  } else {
    t += delta;
  }
  if (t < 0) {
    t = 0;
  }
  if (t > static_cast<int64_t>(kPlayStartDelayMaxSec)) {
    t = static_cast<int64_t>(kPlayStartDelayMaxSec);
  }
  sec = static_cast<uint32_t>(t);
}

static void drawPlayDelayEditScreen(uint32_t sec, int field) {
  auto &d = M5Cardputer.Display;
  d.fillScreen(TFT_BLACK);
  d.setTextDatum(textdatum_t::top_left);
  d.setTextSize(1);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  d.drawString("Play delay  HH:MM:SS", 2, 4);
  d.setTextColor(TFT_DARKGREY, TFT_BLACK);
  d.drawString("Max 24h   [ less   ] more", 2, 14);
  d.drawString("; or . = prev/next field", 2, 24);
  d.drawString("Enter = save   Tab = cancel", 2, 34);
  d.drawString("C/c = countdown HUD on/off", 2, 44);

  char hb[8];
  char mb[8];
  char sb[8];
  const uint32_t h = sec / 3600u;
  const uint32_t m = (sec % 3600u) / 60u;
  const uint32_t s = sec % 60u;
  snprintf(hb, sizeof(hb), "%02u", h);
  snprintf(mb, sizeof(mb), "%02u", m);
  snprintf(sb, sizeof(sb), "%02u", s);

  d.setTextSize(2);
  int y = 62;
  int x = 4;
  d.setTextColor(field == 0 ? TFT_CYAN : TFT_WHITE, TFT_BLACK);
  d.drawString(hb, x, y);
  x += d.textWidth(hb);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  d.drawString(":", x, y);
  x += d.textWidth(":");
  d.setTextColor(field == 1 ? TFT_CYAN : TFT_WHITE, TFT_BLACK);
  d.drawString(mb, x, y);
  x += d.textWidth(mb);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  d.drawString(":", x, y);
  x += d.textWidth(":");
  d.setTextColor(field == 2 ? TFT_CYAN : TFT_WHITE, TFT_BLACK);
  d.drawString(sb, x, y);
  d.setTextSize(1);
}

static void playDelayEditCaptureBaselines() {
  const auto &st = M5Cardputer.Keyboard.keysState();
  bool bu = false;
  bool bd = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.x == 11 && p.y == 1) {
      bu = true;
    }
    if (p.x == 12 && p.y == 1) {
      bd = true;
    }
  }
  bool semiNow = false;
  bool dotNow = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.y == 2 && (p.x == 11 || p.x == 12)) {
      semiNow = true;
    }
    if (p.y == 3 && (p.x == 11 || p.x == 12)) {
      dotNow = true;
    }
  }
  g_pde.bracketUpPrev = bu;
  g_pde.bracketDownPrev = bd;
  g_pde.semiHeldPrev = semiNow;
  g_pde.dotHeldPrev = dotNow;
  g_pde.enterPrev = enterHeldNow(st);
  g_pde.cPrev = menuLetterDownWithFifo('c', 'C');
  g_pde.tabPrev = tabEscBackHeldOnly(st);
}

static void openPlayDelayEdit() {
  g_playDelayEditSec = clampPlayStartDelaySec(g_playStartDelaySec);
  g_playDelayEditField = 2;  // seconds: fastest to tweak for short delays
  g_playDelayEditIgnoreUntilMs = millis() + 450;
  g_playDelayEditOpen = true;
  g_pde = PlayDelayEditKeys{};
  M5Cardputer.update();
  M5Cardputer.Keyboard.updateKeysState();
}

static void closePlayDelayEditSave() {
  g_playStartDelaySec = clampPlayStartDelaySec(g_playDelayEditSec);
  g_playDelayEditOpen = false;
  markMenuSettleAfterModal();
}

static void closePlayDelayEditRevert() {
  g_playDelayEditOpen = false;
  markMenuSettleAfterModal();
}

// Runs in main browser loop while g_playDelayEditOpen (not a blocking modal).
static void tickPlayDelayEdit() {
  drawPlayDelayEditScreen(g_playDelayEditSec, g_playDelayEditField);

  if (millis() < g_playDelayEditIgnoreUntilMs) {
    return;
  }

  if (systemInfoOverlayActive()) {
    return;
  }

  const auto &st = M5Cardputer.Keyboard.keysState();

  if (!g_pde.baselinesSynced) {
    playDelayEditCaptureBaselines();
    g_pde.baselinesSynced = true;
    return;
  }

  const bool tabNow = tabEscBackHeldOnly(st);
  if (tabNow && !g_pde.tabPrev) {
    closePlayDelayEditRevert();
    g_pde.tabPrev = tabNow;
    return;
  }
  g_pde.tabPrev = tabNow;

  const bool cDown = menuLetterDownWithFifo('c', 'C');
  if (cDown && !g_pde.cPrev) {
    g_playStartCountdownHudVisible = !g_playStartCountdownHudVisible;
  }
  g_pde.cPrev = cDown;

  const bool entHeld = enterHeldNow(st);
  const bool entEdge = enterPressedEdgeNow() || (entHeld && !g_pde.enterPrev);
  g_pde.enterPrev = entHeld;
  if (entEdge) {
    closePlayDelayEditSave();
    return;
  }

  bool bracketUpHeld = false;
  bool bracketDownHeld = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.x == 11 && p.y == 1) {
      bracketUpHeld = true;
    }
    if (p.x == 12 && p.y == 1) {
      bracketDownHeld = true;
    }
  }
  const bool buEdge = bracketUpHeld && !g_pde.bracketUpPrev;
  const bool bdEdge = bracketDownHeld && !g_pde.bracketDownPrev;
  g_pde.bracketUpPrev = bracketUpHeld;
  g_pde.bracketDownPrev = bracketDownHeld;
  if (buEdge && !bdEdge) {
    playDelayAdjustField(g_playDelayEditSec, g_playDelayEditField, -1);
  }
  if (bdEdge && !buEdge) {
    playDelayAdjustField(g_playDelayEditSec, g_playDelayEditField, +1);
  }

  bool navSemi = false;
  bool navDot = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if (p.y == 2 && (p.x == 11 || p.x == 12)) {
      navSemi = true;
    }
    if (p.y == 3 && (p.x == 11 || p.x == 12)) {
      navDot = true;
    }
  }
  bool semiHeldNow = false;
  bool dotHeldNow = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.y == 2 && (p.x == 11 || p.x == 12)) {
      semiHeldNow = true;
    }
    if (p.y == 3 && (p.x == 11 || p.x == 12)) {
      dotHeldNow = true;
    }
  }
  const bool semiEdge = semiHeldNow && !g_pde.semiHeldPrev;
  const bool dotEdge = dotHeldNow && !g_pde.dotHeldPrev;
  if (!navSemi && semiEdge) {
    navSemi = true;
  }
  if (!navDot && dotEdge) {
    navDot = true;
  }
  g_pde.semiHeldPrev = semiHeldNow;
  g_pde.dotHeldPrev = dotHeldNow;
  if (navSemi && navDot) {
    navSemi = false;
    navDot = false;
  }
  if (navSemi && !navDot) {
    g_playDelayEditField = (g_playDelayEditField + 2) % 3;
  }
  if (navDot && !navSemi) {
    g_playDelayEditField = (g_playDelayEditField + 1) % 3;
  }
}

// Matches browser top-right + playback S toast (magenta Dly line style).
static void formatDlyLineFromSec(uint32_t sec, char *buf, size_t len) {
  if (sec == 0u) {
    snprintf(buf, len, "Dly off");
  } else {
    char t[16];
    formatHms24(sec, t, sizeof(t));
    snprintf(buf, len, "Dly %s", t);
  }
}

static void drawBrowserTopRightOverlays() {
  auto &d = M5Cardputer.Display;
  constexpr uint16_t kHudPanelBg = 0x18E3u;
  constexpr int kPadX = 8;
  constexpr int kPadY = 6;
  constexpr int kLineStep = 12;
  const bool full = g_playStartCountdownHudVisible;
  const bool preplay = g_browserPreplayActive;
  const bool miniOnly = !full && !preplay;
  const bool preplayBrief = !full && preplay;

  int panelW = 126;
  int panelH = 92;
  if (miniOnly) {
    panelW = 80;
    panelH = 30;
  } else if (preplayBrief) {
    panelW = 112;
    panelH = 48;
  } else if (full && preplay) {
    panelH = 114;
  } else {
    panelH = 104;
  }
  const int x0 = d.width() - panelW - 3;
  constexpr int y0 = 1;
  d.fillRect(x0, y0, panelW, panelH, kHudPanelBg);
  d.drawRect(x0, y0, panelW, panelH, TFT_WHITE);

  const int xrInset = x0 + panelW - kPadX;
  int ty = y0 + kPadY;
  d.setTextDatum(textdatum_t::top_right);
  d.setTextSize(1);

  if (miniOnly) {
    d.setTextColor(0xBDF7u, kHudPanelBg);
    d.drawString("HUD (C)", xrInset, ty);
    ty += kLineStep;
    d.drawString("H hints", xrInset, ty);
  } else if (preplayBrief) {
    char remBuf[16];
    formatHms24(g_browserPreplayRemainSec, remBuf, sizeof(remBuf));
    char leftLine[28];
    snprintf(leftLine, sizeof(leftLine), "Left %s", remBuf);
    d.setTextColor(TFT_CYAN, kHudPanelBg);
    d.drawString(leftLine, xrInset, ty);
    ty += kLineStep;
    d.setTextColor(0xBDF7u, kHudPanelBg);
    d.drawString("HUD (C) open", xrInset, ty);
    ty += kLineStep;
    d.drawString("H hints", xrInset, ty);
  } else {
    d.setTextColor(TFT_YELLOW, kHudPanelBg);
    d.drawString("HUD on (C)", xrInset, ty);
    ty += kLineStep;
    if (preplay) {
      char remBuf[16];
      formatHms24(g_browserPreplayRemainSec, remBuf, sizeof(remBuf));
      char leftLine[28];
      snprintf(leftLine, sizeof(leftLine), "Left %s", remBuf);
      d.setTextColor(TFT_CYAN, kHudPanelBg);
      d.drawString(leftLine, xrInset, ty);
      ty += kLineStep;
    }
    char dlyPart[28];
    formatDlyLineFromSec(g_playStartDelaySec, dlyPart, sizeof(dlyPart));
    d.setTextColor(TFT_MAGENTA, kHudPanelBg);
    d.drawString(dlyPart, xrInset, ty);
    ty += kLineStep;
    d.setTextColor(0xBDF7u, kHudPanelBg);
    d.drawString("D=edit delay", xrInset, ty);
    ty += kLineStep;
    d.drawString("S=start + mark", xrInset, ty);
    ty += kLineStep;
    d.setTextColor(g_loopEnabled ? TFT_GREENYELLOW : 0x94B2u, kHudPanelBg);
    d.drawString(g_loopEnabled ? "Loop ON (L)" : "Loop off (L)", xrInset, ty);
    ty += kLineStep;
    d.setTextColor(g_folderAutoplay ? TFT_GREENYELLOW : 0x94B2u, kHudPanelBg);
    d.drawString(g_folderAutoplay ? "Auto ON (A)" : "Auto off (A)", xrInset, ty);
    ty += kLineStep;
    d.setTextColor(g_sSetMediaPath.length() > 0 ? TFT_GREENYELLOW : 0x94B2u, kHudPanelBg);
    d.drawString(g_sSetMediaPath.length() > 0 ? "Mark: OK" : "Mark: --", xrInset, ty);
    ty += kLineStep;
    d.setTextColor(0xBDF7u, kHudPanelBg);
    d.drawString("H hints", xrInset, ty);
  }
  d.setTextDatum(textdatum_t::top_left);
}

// Big visual countdown for S / Enter pre-play. Drawn over list; HUD draws after.
static void drawBrowserPreplayCountdownBanner() {
  if (!g_browserPreplayActive) {
    return;
  }
  auto &d = M5Cardputer.Display;
  constexpr uint16_t kBarBg = 0x2965u;
  constexpr int kBarY = 54;
  constexpr int kBarH = 50;
  char remBuf[16];
  formatHms24(g_browserPreplayRemainSec, remBuf, sizeof(remBuf));

  d.fillRect(2, kBarY, d.width() - 4, kBarH, kBarBg);
  d.drawRect(2, kBarY, d.width() - 4, kBarH, TFT_CYAN);

  d.setTextDatum(textdatum_t::middle_center);
  d.setTextSize(1);
  d.setTextColor(0xBDF7u, kBarBg);
  d.drawString("Play in (S)  D else 5s", d.width() / 2, kBarY + 10);
  d.setTextSize(2);
  d.setTextColor(TFT_YELLOW, kBarBg);
  d.drawString(remBuf, d.width() / 2, kBarY + 28);
  d.setTextSize(1);
  d.setTextColor(TFT_DARKGREY, kBarBg);
  {
    String bn = displayBasename(g_browserPreplayPath);
    if (bn.length() > 22) {
      bn = bn.substring(0, 19) + "...";
    }
    d.drawString(bn.c_str(), d.width() / 2, kBarY + kBarH - 8);
  }
  d.setTextDatum(textdatum_t::top_left);
}

// listRegionOnly: repaint file rows only — do not wipe footer or right HUD (those caused visible flicker).
static void drawBrowser(const String &cwd, const std::vector<MediaEntry> &entries, int sel, int &scroll,
                        bool listRegionOnly) {
  auto &d = M5Cardputer.Display;
  const bool hudOn = g_playStartCountdownHudVisible;
  const int listY0 = hudOn ? 14 : 46;
  const int listBandPx = MENU_LINES * LINE_H;
  if (entries.empty()) {
    listRegionOnly = false;
  }

  if (!entries.empty()) {
    if (sel < scroll) {
      scroll = sel;
    }
    if (sel >= scroll + MENU_LINES) {
      scroll = sel - MENU_LINES + 1;
    }
  }

  if (listRegionOnly && !entries.empty() && !g_browserPreplayActive && g_browserListPaintedScroll >= 0 &&
      scroll == g_browserListPaintedScroll && sel != g_browserListPaintedSel) {
    const int iOld = g_browserListPaintedSel - scroll;
    const int iNew = sel - scroll;
    if (iOld >= 0 && iOld < MENU_LINES && iNew >= 0 && iNew < MENU_LINES) {
      for (int pass = 0; pass < 2; ++pass) {
        const int idx = (pass == 0) ? iOld : iNew;
        const int i = scroll + idx;
        const int rowY = listY0 + idx * LINE_H;
        d.fillRect(0, rowY, d.width(), LINE_H, TFT_BLACK);
        d.setTextColor(TFT_WHITE, TFT_BLACK);
        d.setTextSize(1);
        const MediaEntry &e = entries[static_cast<size_t>(i)];
        String line = (i == sel ? "> " : "  ");
        if (e.isDir) {
          line += "[";
          line += e.label == ".." ? "up" : "DIR";
          line += "] ";
        }
        line += e.label;
        if (line.length() > 28) {
          line = line.substring(0, 25) + "...";
        }
        d.drawString(line, 2, rowY);
      }
      g_browserListPaintedSel = sel;
      return;
    }
  }

  if (!listRegionOnly) {
    d.fillScreen(TFT_BLACK);
    d.setTextColor(TFT_WHITE, TFT_BLACK);
    d.setTextSize(1);
    {
      String head = cwd.length() > 22 ? String("..") + cwd.substring(cwd.length() - 20) : cwd;
      d.drawString(String("Dir: ") + head, 2, 2);
    }
    if (!hudOn) {
      d.setTextColor(g_loopEnabled ? TFT_GREENYELLOW : TFT_DARKGREY, TFT_BLACK);
      d.drawString(g_loopEnabled ? "Loop: ON (L)" : "Loop: off (L)", 2, 12);
      d.setTextColor(g_folderAutoplay ? TFT_GREENYELLOW : TFT_DARKGREY, TFT_BLACK);
      d.drawString(g_folderAutoplay ? "Auto: ON (A)" : "Auto: off (A)", 2, 22);
      d.setTextColor(g_sSetMediaPath.length() > 0 ? TFT_GREENYELLOW : TFT_DARKGREY, TFT_BLACK);
      d.drawString(g_sSetMediaPath.length() > 0 ? "Mark: OK (S)" : "Mark: --", 2, 32);
    }
    d.setTextColor(TFT_WHITE, TFT_BLACK);
  } else if (!entries.empty()) {
    d.fillRect(0, listY0, d.width(), listBandPx, TFT_BLACK);
    d.setTextColor(TFT_WHITE, TFT_BLACK);
    d.setTextSize(1);
  }

  if (entries.empty()) {
    d.drawString("Empty folder", 2, listY0);
    d.setTextColor(TFT_CYAN, TFT_BLACK);
    if (hudOn) {
      d.drawString("Ent S  Tab  [;. ]  L/A  C=HUD  0/i", 2, d.height() - 10);
    } else {
      d.drawString("Tab  [;. ]  L/A/S/D/C  0/i", 2, d.height() - 10);
    }
    drawBrowserPreplayCountdownBanner();
    drawBrowserTopRightOverlays();
    g_browserListPaintedSel = -1;
    g_browserListPaintedScroll = -1;
    return;
  }

  int y = listY0;
  const int n = static_cast<int>(entries.size());
  for (int i = scroll; i < n && i < scroll + MENU_LINES; i++) {
    const MediaEntry &e = entries[static_cast<size_t>(i)];
    String line = (i == sel ? "> " : "  ");
    if (e.isDir) {
      line += "[";
      line += e.label == ".." ? "up" : "DIR";
      line += "] ";
    }
    line += e.label;
    if (line.length() > 28) {
      line = line.substring(0, 25) + "...";
    }
    d.drawString(line, 2, y);
    y += LINE_H;
  }
  if (!listRegionOnly) {
    d.setTextColor(TFT_CYAN, TFT_BLACK);
    if (hudOn) {
      d.drawString("Ent S  Tab  [;. ]  L/A  C=HUD  0/i", 2, d.height() - 10);
    } else {
      d.drawString("Ent=open  S=cd play  Tab=up  [;. ]  L/A/S/D/C  0/i", 2,
                   d.height() - 10);
    }
    drawBrowserPreplayCountdownBanner();
    drawBrowserTopRightOverlays();
  }
  g_browserListPaintedSel = sel;
  g_browserListPaintedScroll = scroll;
}

// Caller runs M5Cardputer.update(), keyChanged = isChange(), updateKeysState().
// Edge-detect L/A so keyboard repeat does not spin (continues that skip delay(10) → WDT reset).
static MenuAction pollMenuKeys(bool keyChanged, bool &toggleLPrev, bool &toggleAPrev) {
  const auto &st = M5Cardputer.Keyboard.keysState();
  static bool enterPrevHeld = false;
  static bool bracketUpPrevHeld = false;
  static bool bracketDownPrevHeld = false;
  static bool semiHeldPrev = false;
  static bool dotHeldPrev = false;
  static constexpr size_t kMenuPressCap = 24;
  static bool toggleDPrev = false;
  static bool toggleCPrev = false;
  static bool s_browserEnterCellListPrev = false;
  static bool menuTabEscBackPrevHeld = false;

  // If the keyboard reader may have left nav keys electrically "stuck" across a
  // screen/UI transition (Tab/Esc, playback exit), reset the edge baselines
  // *before* any early returns so list navigation can't appear frozen.
  if (g_menuResetListNavEdgesOnNextPoll) {
    // Match current held state to avoid a fake held->edge transition
    // on the very next poll.
    bool bracketUpHeldNow = false;
    bool bracketDownHeldNow = false;
    bool semiHeldNow = false;
    bool dotHeldNow = false;
    for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
      if (p.x == 11 && p.y == 1) {
        bracketUpHeldNow = true;
      }
      if (p.x == 12 && p.y == 1) {
        bracketDownHeldNow = true;
      }
      if (p.y == 2 && (p.x == 11 || p.x == 12)) {
        semiHeldNow = true;
      }
      if (p.y == 3 && (p.x == 11 || p.x == 12)) {
        dotHeldNow = true;
      }
    }
    bracketUpPrevHeld = bracketUpHeldNow;
    bracketDownPrevHeld = bracketDownHeldNow;
    semiHeldPrev = semiHeldNow;
    dotHeldPrev = dotHeldNow;
    g_menuResetListNavEdgesOnNextPoll = false;
  }
  // Browser Tab/up-dir/long-press: matrix only. tabEscHeldNow() includes hid_keys ESC which ghosts on
  // Cardputer → false Tab-down edge then spurious long-Tab behavior without touching S.
  const bool tabPhyNow = tabKeyHeldPhysical();
  if (g_menuSyncTabEscBackBaselineOnNextPoll) {
    menuTabEscBackPrevHeld = tabPhyNow;
    g_menuSyncTabEscBackBaselineOnNextPoll = false;
  }
  if (g_menuSyncEnterEdgeOnNextPoll) {
    enterPrevHeld = enterHeldNow(st);
    bool elSync = false;
    for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
      if (p.x == 13 && p.y == 2) {
        elSync = true;
        break;
      }
    }
    s_browserEnterCellListPrev = elSync;
    g_menuSyncEnterEdgeOnNextPoll = false;
  }

  if (g_menuSuppressTabEscUpDir) {
    const uint32_t tm = millis();
    if (!tabPhyNow ||
        static_cast<uint32_t>(tm - g_menuTabSuppressArmMs) >= kMenuTabSuppressForceReleaseMs) {
      g_menuSuppressTabEscUpDir = false;
    }
  }
  if (g_menuSuppressEnterUntilRelease) {
    const bool enterNow = enterHeldNow(st);
    const uint32_t enterGuardAge = static_cast<uint32_t>(millis() - g_menuSuppressEnterArmMs);
    if (g_menuSuppressEnterPlayback) {
      if (!enterNow || enterGuardAge >= 550u) {
        g_menuSuppressEnterUntilRelease = false;
        g_menuSuppressEnterPlayback = false;
      }
    } else if (!enterNow || enterGuardAge >= 220u) {
      g_menuSuppressEnterUntilRelease = false;
    }
  }

  // Snapshot pressEvents before L/A so a single S press is not lost to ghost L/A consuming the frame.
  Point2D_t menuPressBuf[kMenuPressCap];
  size_t menuPressN = 0;
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    if (menuPressN < kMenuPressCap) {
      menuPressBuf[menuPressN++] = p;
    }
  }
  bool sFifo = false;
  bool enterFifo = false;
  bool dFifo = false;
  bool cFifo = false;
  bool sFifoKeyCell = false;
  bool hFifoHint = false;
  for (size_t pi = 0; pi < menuPressN; ++pi) {
    const Point2D_t &p = menuPressBuf[pi];
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    if (browserHintHKeyAtPoint(p)) {
      hFifoHint = true;
    }
    if (browserMatrixCellIsTimerPlayS(p)) {
      sFifoKeyCell = true;
    }
    if (browserMatrixCellIsTimerPlayS(p) || browserMenuKeyMeansS(kch, kv)) {
      sFifo = true;
    }
    if (p.x == 13 && p.y == 2) {
      enterFifo = true;
    }
    if (kch == static_cast<uint8_t>('d') || kch == static_cast<uint8_t>('D')) {
      dFifo = true;
    }
    if (kch == static_cast<uint8_t>('c') || kch == static_cast<uint8_t>('C')) {
      cFifo = true;
    }
    if (kv.value_first == 'd' || kv.value_second == 'd' || kv.value_first == 'D' ||
        kv.value_second == 'D') {
      dFifo = true;
    }
    if (kv.value_first == 'c' || kv.value_second == 'c' || kv.value_first == 'C' ||
        kv.value_second == 'C') {
      cFifo = true;
    }
  }
  {
    bool enterCellList = false;
    for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
      if (p.x == 13 && p.y == 2) {
        enterCellList = true;
        break;
      }
    }
    s_browserEnterCellListPrev = enterCellList;
  }
  bool sKeyCellNow = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserMatrixCellIsTimerPlayS(p)) {
      sKeyCellNow = true;
      break;
    }
  }
  static bool s_browserSKeyCellRawPrev = false;
  static uint8_t s_browserSKeyRawOpenStreak = 0;
  if (!sKeyCellNow) {
    if (s_browserSKeyRawOpenStreak < 255) {
      s_browserSKeyRawOpenStreak++;
    }
    if (s_browserSKeyRawOpenStreak >= 2) {
      s_browserSKeyCellRawPrev = false;
    }
  } else {
    s_browserSKeyRawOpenStreak = 0;
  }
  bool sHeldMatrix = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (browserMatrixCellIsTimerPlayS(p)) {
      sHeldMatrix = true;
      break;
    }
    const uint8_t km = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kvm = M5Cardputer.Keyboard.getKeyValue(p);
    if (browserMenuKeyMeansS(km, kvm)) {
      sHeldMatrix = true;
      break;
    }
  }
  const bool sHeldDriver =
      M5Cardputer.Keyboard.isKeyPressed('s') || M5Cardputer.Keyboard.isKeyPressed('S');
  // Matrix and isKeyPressed diverge after preplay/codec work; tracking only the matrix made the 2nd+ S
  // press invisible when the driver still saw 's' (no rise edge, keyChanged often false).
  const bool sHeldAny = sHeldMatrix || sHeldDriver;
  // keyList can ghost (3,2) without any real S decode — that latched s_browserSKeyCellPrev true and
  // blocked every later press. Only treat the cell as "down" when matrix/driver agree.
  const bool sKeySolid = sKeyCellNow && sHeldAny;
  static bool s_browserSKeyCellPrev = false;
  static uint8_t s_browserSKeyOpenStreak = 0;
  if (!sKeySolid) {
    if (s_browserSKeyOpenStreak < 255) {
      s_browserSKeyOpenStreak++;
    }
    if (s_browserSKeyOpenStreak >= 2) {
      s_browserSKeyCellPrev = false;
    }
  } else {
    s_browserSKeyOpenStreak = 0;
  }
  bool sWordHas = false;
  for (char c : st.word) {
    if (c == 's' || c == 'S') {
      sWordHas = true;
      break;
    }
  }
  static bool s_browserMenuPrevWordHadS = false;
  static bool s_browserSHeldDriverPrev = false;

  if (g_menuResetBrowserLetterTogglesOnNextPoll) {
    g_browserTimerPlayLastMs = 0;
    // Force edges to be re-armed regardless of any ghost/stuck held state.
    toggleDPrev = false;
    toggleCPrev = false;
    {
      bool elR = false;
      for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
        if (p.x == 13 && p.y == 2) {
          elR = true;
          break;
        }
      }
      s_browserEnterCellListPrev = elR;
    }
    // H hint: do not zero g_browserMainListHKeyPrev here. After MP3/I2S, row-2 often ghosts (7,2) and
    // S in the same FIFO — matrixRise looked true with sFifo also true, hint was blocked by !sFifo but
    // prev still latched true at end of the hint block → no further H edges. Resync snaps baselines to
    // actual relaxedNow/hFifoHint the same poll (no fake rise).
    s_browserHintResyncHBaselineNextPoll = true;
    s_browserMenuPrevWordHadS = sWordHas;
    s_browserSKeyCellPrev = sKeySolid;
    s_browserSKeyCellRawPrev = sKeyCellNow;
    // Sync to actual held: `false` here made the next poll think S had "just gone down" when it was
    // still ghost-held, and pairing with g_browserTimerPlayForceNextSDown disabled sRiseHeldEdge — S
    // worked once (force false at boot) then never again until power cycle.
    g_browserTimerPlaySPrevHeld = sHeldAny;
    s_browserSHeldDriverPrev = sHeldDriver;
    g_menuResetBrowserLetterTogglesOnNextPoll = false;
  }
  const bool sRiseHeldEdge = sHeldAny && !g_browserTimerPlaySPrevHeld;
  g_browserTimerPlaySPrevHeld = sHeldAny;

  const bool dHeldDriver =
      M5Cardputer.Keyboard.isKeyPressed('d') || M5Cardputer.Keyboard.isKeyPressed('D');
  bool cHeldMatrix = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    const uint8_t km = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kvm = M5Cardputer.Keyboard.getKeyValue(p);
    if (browserMenuKeyMeansC(km, kvm)) {
      cHeldMatrix = true;
      break;
    }
  }
  const bool cHeldLevel = cHeldMatrix;
  const bool sKeyCellPressEdge = sKeySolid && !s_browserSKeyCellPrev;
  const bool sDriverPressEdge = sHeldDriver && !s_browserSHeldDriverPrev;
  s_browserMenuPrevWordHadS = sWordHas;
  const uint32_t nowTp = millis();
  // After a clean S release, drop list timer-play cooldown so the next tap is not blocked by a
  // cancelled preplay (still had set lastMs) or ghost double-fires.
  static uint8_t s_browserListSReleaseStreak = 0;
  if (!sHeldAny) {
    if (s_browserListSReleaseStreak < 255) {
      s_browserListSReleaseStreak++;
    }
    if (s_browserListSReleaseStreak >= 2) {
      g_browserTimerPlayLastMs = 0u;
    }
  } else {
    s_browserListSReleaseStreak = 0;
  }
  // Tab → UP_DIR before TIMER_PLAY_FILE: same scan often delivers ghost S in pressEvents or a false S
  // edge when Tab is pressed → spurious preplay countdown ("delay screen").
  const bool tabDownEdgeMenu = tabPhyNow && !s_menuTabWasDown;
  if (tabDownEdgeMenu && !g_menuSuppressTabEscUpDir) {
    const uint32_t nowTabDn = millis();
    if (static_cast<uint32_t>(nowTabDn - g_menuLastBrowserUpDirMs) < kMenuBrowserUpDirMinGapMs) {
      menuTabEscBackPrevHeld = tabPhyNow;
    } else {
      g_menuLastBrowserUpDirMs = nowTabDn;
      g_menuTabSuppressArmMs = nowTabDn;
      bool bracketUpHeldNow = false;
      bool bracketDownHeldNow = false;
      bool semiHeldNow = false;
      bool dotHeldNow = false;
      for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
        if (p.x == 11 && p.y == 1) {
          bracketUpHeldNow = true;
        }
        if (p.x == 12 && p.y == 1) {
          bracketDownHeldNow = true;
        }
        if (p.y == 2 && (p.x == 11 || p.x == 12)) {
          semiHeldNow = true;
        }
        if (p.y == 3 && (p.x == 11 || p.x == 12)) {
          dotHeldNow = true;
        }
      }
      bracketUpPrevHeld = bracketUpHeldNow;
      bracketDownPrevHeld = bracketDownHeldNow;
      semiHeldPrev = semiHeldNow;
      dotHeldPrev = dotHeldNow;
      g_menuSuppressTabEscUpDir = true;
      g_menuResetListNavEdgesOnNextPoll = false;
      menuTabEscBackPrevHeld = false;
      s_menuTabWasDown = true;
      // Same scan can ghost S; latch prev so next poll does not treat it as a new S press.
      s_browserSKeyCellPrev = sKeySolid;
      s_browserSKeyCellRawPrev = sKeyCellNow;
      s_browserSHeldDriverPrev = sHeldDriver;
      // UP_DIR returns before the hint block — H prev/FIFO baseline would stay stale one poll while
      // Tab scan ghosts row-2; next poll then latches wrong or blocks toggles (same class as post-MP3).
      {
        const bool relaxedNowH =
            menuLetterDownWithFifo('h', 'H') || browserHintHMatrixHeldNow();
        g_browserMainListHKeyPrev = relaxedNowH;
        s_browserHintHFifoPrev = hFifoHint;
      }
      s_browserHintResyncHBaselineNextPoll = false;
      return MenuAction::UP_DIR;
    }
  }
  // Keys hint: must run after Tab→UP_DIR — same scan can put ghost (7,2) in FIFO with Tab; hint was
  // winning first. Do not gate on tabPhyNow: matrix Tab often sticks "down" after Tab (see preplay
  // comment on st.tab) and then !tabPhyNow blocks every H toggle until reboot.
  // Rise = new press in FIFO (relaxed cell) OR relaxed matrix edge. Strict-only matrix missed ADV H;
  // sticky relaxed-only latched forever on ghost (7,2). keysHintOnHKey sets resync to snap prev after toggle.
  {
    const bool enterBlocksHint = enterFifo;
    const bool relaxedNow =
        menuLetterDownWithFifo('h', 'H') || browserHintHMatrixHeldNow();
    if (s_browserHintResyncHBaselineNextPoll) {
      g_browserMainListHKeyPrev = relaxedNow;
      s_browserHintHFifoPrev = hFifoHint;
      s_browserHintResyncHBaselineNextPoll = false;
    }
    const bool prevRelax = g_browserMainListHKeyPrev;
    const bool fifoRise = hFifoHint && !s_browserHintHFifoPrev;
    s_browserHintHFifoPrev = hFifoHint;
    const bool matrixRise = relaxedNow && !prevRelax;
    g_browserMainListHKeyPrev = relaxedNow;
    const bool hHintRisePoll = (fifoRise || matrixRise) && !enterBlocksHint && !sFifo;
    if (hHintRisePoll) {
      return MenuAction::SHOW_KEYS_HINT;
    }
  }
  // Stable S: physical cell (3,2) press edge + FIFO + open-streak watchdog (above). isChange() optional.
  // See browserTabOrEscBlocksTimerPlayS — timer S is not suppressed by hid Esc (Cardputer hid_keys quirk).
  if (!browserTabOrEscBlocksTimerPlayS(st)) {
    // isKeyPressed('s') often sticks down after codec/preplay; then sRiseHeldEdge never refires and
    // sKeySolid stays false if the matrix missed a scan — S looked one-shot. Raw matrix edge + driver
    // edge + FIFO cover repeat presses. sRiseHeldEdge must count even when forceNextS is set: otherwise
    // after playback/Tab, keyChanged is usually false and S only worked once until reboot.
    // Omit sKeyCellRawEdge (matrix noise). Omit sWordRise (st.word often ghosts 's' after first use).
    // Omit (keyChanged && sHeldAny): after playback/Tab, isChange() + ghost S looked like an S press.
    // Force widens only to real S in pressEvents — never keyChanged && sKeyCellNow alone.
    const bool sTimerTrigger =
        sFifo || sFifoKeyCell || sKeyCellPressEdge || sDriverPressEdge || sRiseHeldEdge ||
        (g_browserTimerPlayForceNextSDown && (sFifo || sFifoKeyCell));
    const bool sTimerCooldown =
        g_browserTimerPlayLastMs != 0u &&
        (nowTp - g_browserTimerPlayLastMs) < kBrowserListTimerPlayCooldownMs;
    if (sTimerTrigger && !sTimerCooldown) {
      g_browserTimerPlayForceNextSDown = false;
      g_browserTimerPlayLastMs = nowTp;
      s_browserSKeyCellPrev = sKeySolid;
      s_browserSKeyCellRawPrev = sKeyCellNow;
      s_browserSHeldDriverPrev = sHeldDriver;
      return MenuAction::TIMER_PLAY_FILE;
    }
  }
  s_browserSKeyCellPrev = sKeySolid;
  s_browserSKeyCellRawPrev = sKeyCellNow;
  s_browserSHeldDriverPrev = sHeldDriver;
  const bool lDown = M5Cardputer.Keyboard.isKeyPressed('l') || M5Cardputer.Keyboard.isKeyPressed('L');
  if (lDown && !toggleLPrev) {
    toggleLPrev = true;
    return MenuAction::TOGGLE_LOOP;
  }
  if (!lDown) {
    toggleLPrev = false;
  }
  const bool aDown = M5Cardputer.Keyboard.isKeyPressed('a') || M5Cardputer.Keyboard.isKeyPressed('A');
  if (aDown && !toggleAPrev) {
    toggleAPrev = true;
    return MenuAction::TOGGLE_AUTOPLAY;
  }
  if (!aDown) {
    toggleAPrev = false;
  }
  // Latch clear on physical release only for D/C (see pressEvents snapshot + toggle notes above).
  const bool dDown = dHeldDriver || dFifo;
  if (dDown && !toggleDPrev) {
    toggleDPrev = true;
    return MenuAction::OPEN_DELAY_EDITOR;
  }
  if (!dHeldDriver) {
    toggleDPrev = false;
  }
  bool cWord = false;
  for (char c : st.word) {
    if (c == 'c' || c == 'C') {
      cWord = true;
      break;
    }
  }
  const bool cHeldDriver = M5Cardputer.Keyboard.isKeyPressed('c') || M5Cardputer.Keyboard.isKeyPressed('C');
  if (g_browserHudForceNextCDown && (cFifo || cHeldLevel || cHeldDriver || cWord)) {
    g_browserHudForceNextCDown = false;
    toggleCPrev = true;
    return MenuAction::TOGGLE_COUNTDOWN_HUD;
  }
  if ((cFifo || (keyChanged && cHeldDriver)) && !toggleCPrev) {
    toggleCPrev = true;
    return MenuAction::TOGGLE_COUNTDOWN_HUD;
  }
  if (!cFifo && !cHeldDriver && !cHeldLevel) {
    toggleCPrev = false;
  }

  menuTabEscBackPrevHeld = tabPhyNow;
  s_menuTabWasDown = tabPhyNow;

  // Enter in browser:
  // - accept physical press-edge when available
  // - fall back to held-state rising-edge if pressEvents are throttled
  // - rate-limit slightly to avoid accidental double-open
  const bool enterHeld = enterHeldNow(st);
  const bool enterEdge = enterFifo;
  const bool enterRising = enterHeld && !enterPrevHeld;
  enterPrevHeld = enterHeld;
  if (!g_menuSuppressEnterUntilRelease && (enterEdge || enterRising)) {
    const uint32_t now = millis();
    if ((now - g_menuLastEnterAtMs) >= kMenuEnterMinGapMs) {
      g_menuLastEnterAtMs = now;
      return MenuAction::ENTER;
    }
  }

  // List UP/DOWN:
  // - `[` / `]` : keyList() edges (row 1).
  // - `;` / `.` : keyList() edges only. We do NOT use pressEvents for list nav: the TCA8418 FIFO
  //   can emit many events per held key / boot noise → highlight "walks" nonstop.
  bool navUpNow = false;
  bool navDownNow = false;

  bool bracketUpHeldNow = false;    // '[' cell
  bool bracketDownHeldNow = false;  // ']' cell
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.x == 11 && p.y == 1) {
      bracketUpHeldNow = true;
    } else if (p.x == 12 && p.y == 1) {
      bracketDownHeldNow = true;
    }
  }

  const bool bracketUpEdge = bracketUpHeldNow && !bracketUpPrevHeld;
  const bool bracketDownEdge = bracketDownHeldNow && !bracketDownPrevHeld;
  navUpNow = navUpNow || bracketUpEdge;
  navDownNow = navDownNow || bracketDownEdge;

  // `;` (row 2 cols 11–12) / `.` (row 3 cols 11–12): rising edge on keyList only.
  bool semiHeldNow = false;
  bool dotHeldNow = false;
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if (p.y == 2 && (p.x == 11 || p.x == 12)) {
      semiHeldNow = true;
    }
    if (p.y == 3 && (p.x == 11 || p.x == 12)) {
      dotHeldNow = true;
    }
  }
  const bool semiEdge = semiHeldNow && !semiHeldPrev;
  const bool dotEdge = dotHeldNow && !dotHeldPrev;
  if (!navUpNow && semiEdge) {
    navUpNow = true;
  }
  if (!navDownNow && dotEdge) {
    navDownNow = true;
  }

  // Ghost/overlap safety: if both asserted from one scan, cancel.
  if (navUpNow && navDownNow) {
    navUpNow = false;
    navDownNow = false;
  }

  bracketUpPrevHeld = bracketUpHeldNow;
  bracketDownPrevHeld = bracketDownHeldNow;
  semiHeldPrev = semiHeldNow;
  dotHeldPrev = dotHeldNow;

  if (navUpNow) {
    return MenuAction::UP;
  }
  if (navDownNow) {
    return MenuAction::DOWN;
  }
  return MenuAction::NONE;
}

static bool playbackSeekSuppressedNow() {
  return playbackVolumeKeysHeldNow() ||
         ((g_lastVolumeStepMs != 0u) &&
          (static_cast<int32_t>(millis() - g_lastVolumeStepMs) >= 0) &&
          (millis() - g_lastVolumeStepMs < kVolumeGhostSuppressSeekMs));
}

// If pollPlaybackKeys missed a ,/</ or /? edge (common while decoding video), recover from raw keys.
static PlayKey augmentPlayKeyWithVideoSeekRaw(PlayKey pk) {
  const bool cHeld =
      M5Cardputer.Keyboard.isKeyPressed(',') || M5Cardputer.Keyboard.isKeyPressed('<');
  const bool sHeld =
      M5Cardputer.Keyboard.isKeyPressed('/') || M5Cardputer.Keyboard.isKeyPressed('?');
  const bool cRiseRaw = cHeld && !g_videoSeekRawPrevComma;
  const bool sRiseRaw = sHeld && !g_videoSeekRawPrevSlash;
  if (pk == PlayKey::NONE && !playbackSeekSuppressedNow()) {
    if (cRiseRaw && !sRiseRaw) {
      pk = PlayKey::SEEK_LEFT;
    } else if (sRiseRaw && !cRiseRaw) {
      pk = PlayKey::SEEK_RIGHT;
    }
  }
  g_videoSeekRawPrevComma = cHeld;
  g_videoSeekRawPrevSlash = sHeld;
  return pk;
}

// TCA8418 press FIFO: last unambiguous ,/</ vs /? wins. Catches taps pollPlaybackKeys sometimes drops.
static PlayKey pollMjpegSeekFromPressFifo() {
  if (playbackSeekSuppressedNow()) {
    return PlayKey::NONE;
  }
  int dir = 0;
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
    const bool leftHere =
        (kch == static_cast<uint8_t>(',') || kch == static_cast<uint8_t>('<') ||
         kv.value_first == ',' || kv.value_second == ',' || kv.value_first == '<' ||
         kv.value_second == '<');
    const bool rightHere =
        (kch == static_cast<uint8_t>('/') || kch == static_cast<uint8_t>('?') ||
         kv.value_first == '/' || kv.value_second == '/' || kv.value_first == '?' ||
         kv.value_second == '?');
    if (leftHere && !rightHere) {
      dir = -1;
    } else if (rightHere && !leftHere) {
      dir = 1;
    }
  }
  if (dir < 0) {
    return PlayKey::SEEK_LEFT;
  }
  if (dir > 0) {
    return PlayKey::SEEK_RIGHT;
  }
  return PlayKey::NONE;
}

// Caller runs M5Cardputer.update(), then Keyboard.updateKeysState(), then keyChanged = isChange()
// (same order as MP3 path). If !keyChanged but pressEvents is non-empty, still evaluate seek so keys
// are not dropped when an extra updateKeysState() ran before polling (video outer loop).
static PlayKey pollPlaybackKeys(bool keyChanged, bool &backArmed, bool &backPrevHeld,
                                uint32_t playbackStartMs) {
  pollVolumeKeysMatrix(nullptr);

  if (M5Cardputer.BtnA.wasClicked()) {
    return PlayKey::PAUSE_TOGGLE;
  }

  const auto &st = M5Cardputer.Keyboard.keysState();

  const bool hHeldStrict = playbackKeysHintHHeldStrictNow();
  const bool enterBlocksHint = enterHeldNow(st) || enterPressedEdgeNow();
  if (hHeldStrict && !g_playbackPollHPrev && !enterBlocksHint) {
    g_playbackPollHPrev = true;
    return PlayKey::SHOW_KEYS_HINT;
  }
  if (!hHeldStrict) {
    g_playbackPollHPrev = false;
  }

  if (playbackBackEdge(st, backArmed, backPrevHeld, playbackStartMs)) {
    return PlayKey::BACK_MENU;
  }
  const PlayKey nb = pollTrackNavNextPrev();
  if (nb == PlayKey::TRACK_NEXT || nb == PlayKey::TRACK_PREV) {
    return nb;
  }

  const bool commaSeekHeldNow =
      M5Cardputer.Keyboard.isKeyPressed(',') || M5Cardputer.Keyboard.isKeyPressed('<');
  const bool slashSeekHeldNow =
      M5Cardputer.Keyboard.isKeyPressed('/') || M5Cardputer.Keyboard.isKeyPressed('?');
  const bool commaSeekRise = commaSeekHeldNow && !g_seekCommaPrevHeld;
  const bool slashSeekRise = slashSeekHeldNow && !g_seekSlashPrevHeld;
  g_seekCommaPrevHeld = commaSeekHeldNow;
  g_seekSlashPrevHeld = slashSeekHeldNow;

  const bool sDownP = menuLetterDownWithFifo('s', 'S');
  if (sDownP && !g_playbackPollSPrev) {
    g_playbackPollSPrev = true;
    return PlayKey::S_SET_MEDIA;
  }
  if (!sDownP) {
    g_playbackPollSPrev = false;
  }

  if (!keyChanged && M5Cardputer.Keyboard.pressEvents().empty() && !commaSeekRise && !slashSeekRise) {
    return PlayKey::NONE;
  }
  if (keyChanged) {
    const uint32_t now = millis();
    for (char c : st.word) {
      if (c == 'p' || c == 'P') {
        if (static_cast<int32_t>(now - g_ignorePauseToggleUntilMs) < 0) {
          break;
        }
        return PlayKey::PAUSE_TOGGLE;
      }
      if (c == 'l' || c == 'L') {
        return PlayKey::TOGGLE_LOOP;
      }
      if (c == 'a' || c == 'A') {
        return PlayKey::TOGGLE_AUTOPLAY;
      }
    }
  }

  const bool suppressSeek = playbackSeekSuppressedNow();

  if (!suppressSeek) {
    auto classifySeekPress = [](const Point2D_t &p) -> int {
      const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
      const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
      const bool leftHere =
          (kch == static_cast<uint8_t>(',') || kch == static_cast<uint8_t>('<') ||
           kv.value_first == ',' || kv.value_second == ',' || kv.value_first == '<' ||
           kv.value_second == '<');
      const bool rightHere =
          (kch == static_cast<uint8_t>('/') || kch == static_cast<uint8_t>('?') ||
           kv.value_first == '/' || kv.value_second == '/' || kv.value_first == '?' ||
           kv.value_second == '?');
      if (leftHere && !rightHere) {
        return -1;
      }
      if (rightHere && !leftHere) {
        return 1;
      }
      return 0;
    };

    // Rising edges beat stuck ghost keys on the same row.
    if (commaSeekRise && !slashSeekRise) {
      return PlayKey::SEEK_LEFT;
    }
    if (slashSeekRise && !commaSeekRise) {
      return PlayKey::SEEK_RIGHT;
    }
    if (commaSeekRise && slashSeekRise) {
      int peSeekDir = 0;
      for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
        const int d = classifySeekPress(p);
        if (d != 0 && peSeekDir == 0) {
          peSeekDir = d;
        }
      }
      if (peSeekDir < 0) {
        return PlayKey::SEEK_LEFT;
      }
      if (peSeekDir > 0) {
        return PlayKey::SEEK_RIGHT;
      }
    }

    const bool wantPressOrWordSeek = keyChanged || !M5Cardputer.Keyboard.pressEvents().empty();
    if (wantPressOrWordSeek) {
      int peSeekDir = 0;
      for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
        const int d = classifySeekPress(p);
        if (d != 0 && peSeekDir == 0) {
          peSeekDir = d;
        }
      }
      if (peSeekDir < 0) {
        return PlayKey::SEEK_LEFT;
      }
      if (peSeekDir > 0) {
        return PlayKey::SEEK_RIGHT;
      }
    }

    if (keyChanged) {
      int firstLeftPos = -1;
      int firstRightPos = -1;
      {
        int wi = 0;
        for (char c : st.word) {
          if (c == ',' || c == '<' || c == '.' || c == '>') {
            if (firstLeftPos < 0) {
              firstLeftPos = wi;
            }
          } else if (c == '/' || c == '?') {
            if (firstRightPos < 0) {
              firstRightPos = wi;
            }
          }
          ++wi;
        }
      }
      if (firstLeftPos >= 0 && firstRightPos < 0) {
        return PlayKey::SEEK_LEFT;
      }
      if (firstRightPos >= 0 && firstLeftPos < 0) {
        return PlayKey::SEEK_RIGHT;
      }
      if (firstLeftPos >= 0 && firstRightPos >= 0) {
        if (firstRightPos < firstLeftPos) {
          return PlayKey::SEEK_RIGHT;
        }
        if (firstLeftPos < firstRightPos) {
          return PlayKey::SEEK_LEFT;
        }
      }
    }

    if (hidHas(st.hid_keys, HID_LEFT) && !hidHas(st.hid_keys, HID_RIGHT)) {
      return PlayKey::SEEK_LEFT;
    }
    if (hidHas(st.hid_keys, HID_RIGHT) && !hidHas(st.hid_keys, HID_LEFT)) {
      return PlayKey::SEEK_RIGHT;
    }
  }
  return PlayKey::NONE;
}

static void applySeekForward(File &v, File &pcm, bool pcmOpen, int &nextFrameIdx) {
  M5Cardputer.Speaker.stop();
  for (int s = 0; s < SEEK_FRAMES; s++) {
    if (!skipOneJpegFrame(v)) {
      break;
    }
    nextFrameIdx++;
  }
  if (pcmOpen) {
    const size_t off = static_cast<size_t>(nextFrameIdx) * AUDIO_CHUNK;
    pcm.seek(off < pcm.size() ? off : pcm.size());
  }
}

// Show the frame at the current file position right after a seek (otherwise the old JPEG stays up
// until the next outer-loop decode, so it looks like the video did not jump ~5s).
static void displayOneFrameAfterSeek(File &v, int &nextFrameIdx) {
  while (v.available()) {
    if (g_mjpeg.readMjpegBuf()) {
      g_mjpeg.drawJpg();
      nextFrameIdx++;
      return;
    }
  }
}

static bool applySeekBack(const String &videoPath, const String &pcmPath, File &v, File &pcm,
                          bool &pcmOpen, int &nextFrameIdx) {
  nextFrameIdx -= SEEK_BACK_FRAMES;
  if (nextFrameIdx < 0) {
    nextFrameIdx = 0;
  }
  return jumpToVideoFrame(videoPath, pcmPath, v, pcm, pcmOpen, nextFrameIdx);
}

static bool waitFramePace(bool waitSpeaker, bool &playing, uint32_t &frameStartMs,
                          const String &videoPath, const String &pcmPath, File &v, File &pcm,
                          bool &pcmOpen, int &nextFrameIdx, bool &backArmed,
                          bool &backPrevHeld, uint32_t playbackStartMs) {
  for (;;) {
    M5Cardputer.update();
    M5Cardputer.Keyboard.updateKeysState();
    const bool keyChanged = M5Cardputer.Keyboard.isChange();
    if (systemInfoOverlayActive()) {
      if (pcmOpen) {
        M5Cardputer.Speaker.stop();
      }
      drawSystemInfoScreen();
      delay(20);
      frameStartMs = millis();
      continue;
    }

    PlayKey pk = pollPlaybackKeys(keyChanged, backArmed, backPrevHeld, playbackStartMs);
    pk = augmentPlayKeyWithVideoSeekRaw(pk);
    if (pk == PlayKey::NONE || pk == PlayKey::SEEK_LEFT || pk == PlayKey::SEEK_RIGHT) {
      const PlayKey fk = pollMjpegSeekFromPressFifo();
      if (fk != PlayKey::NONE) {
        pk = fk;
      }
    }
    drawMp3LoopHintTick();
    drawSetBookmarkHintTick();
    drawMp3VolumeHintTick();
    drawKeysHintOverlayTick(nullptr);

    if (pk == PlayKey::SHOW_KEYS_HINT) {
      keysHintOnHKey(nullptr);
      continue;
    }
    if (pk == PlayKey::BACK_MENU) {
      return false;
    }
    if (pk == PlayKey::S_SET_MEDIA) {
      g_sSetMediaPath = videoPath;
      showSetBookmarkHintNow();
      continue;
    }
    if (pk == PlayKey::PAUSE_TOGGLE) {
      playing = !playing;
    }
    if (pk == PlayKey::TOGGLE_LOOP) {
      g_loopEnabled = !g_loopEnabled;
      Serial.printf("Loop %s\n", g_loopEnabled ? "ON" : "OFF");
      showLoopHintNow();
      continue;
    }
    if (pk == PlayKey::TOGGLE_AUTOPLAY) {
      g_folderAutoplay = !g_folderAutoplay;
      Serial.printf("Folder autoplay %s\n", g_folderAutoplay ? "ON" : "OFF");
      continue;
    }
    if (pk == PlayKey::SEEK_RIGHT) {
      applySeekForward(v, pcm, pcmOpen, nextFrameIdx);
      displayOneFrameAfterSeek(v, nextFrameIdx);
      frameStartMs = millis();
      continue;
    }
    if (pk == PlayKey::SEEK_LEFT) {
      if (!applySeekBack(videoPath, pcmPath, v, pcm, pcmOpen, nextFrameIdx)) {
        return false;
      }
      displayOneFrameAfterSeek(v, nextFrameIdx);
      frameStartMs = millis();
      continue;
    }
    if (pk == PlayKey::TRACK_NEXT) {
      g_videoTrackNavRequest = +1;
      return false;
    }
    if (pk == PlayKey::TRACK_PREV) {
      g_videoTrackNavRequest = -1;
      return false;
    }

    if (!playing) {
      return true;
    }

    const bool busy = waitSpeaker && M5Cardputer.Speaker.isPlaying();
    const bool timeOk = (millis() - frameStartMs) >= FRAME_MS;
    if (!busy && timeOk) {
      return true;
    }
    delay(1);
  }
}

static PlayExit playVideoFile(const String &videoPath) {
  File v = SD.open(videoPath.c_str(), FILE_READ);
  if (!v || v.isDirectory()) {
    Serial.printf("Cannot open %s\n", videoPath.c_str());
    markPlaybackReturnedToMenu();
    return PlayExit::MENU;
  }

  const String pcmPath = pcmPathForMjpeg(videoPath);
  File pcmFile;
  bool pcmOpen = false;
  if (SD.exists(pcmPath.c_str())) {
    pcmFile = SD.open(pcmPath.c_str(), FILE_READ);
    if (pcmFile && !pcmFile.isDirectory() && pcmFile.size() > 0) {
      pcmOpen = true;
      Serial.printf("Audio %s\n", pcmPath.c_str());
    } else {
      if (pcmFile) {
        pcmFile.close();
      }
    }
  }

  Serial.printf("Playing %s\n", videoPath.c_str());

  M5Cardputer.Speaker.begin();
  setSpeakerVolumePersisted(g_speakerVolumePersist);

  g_mjpeg.reset();
  g_mjpeg.setup(v, g_mjpegBuf, &M5Cardputer.Display, false);

  resetPlaybackKeyboardBaselines();
  M5Cardputer.update();
  M5Cardputer.Keyboard.updateKeysState();
  (void)M5Cardputer.Keyboard.isChange();
  syncPlaybackKeysHintPollPrevAfterKeyboardUpdate();

  bool playing = true;
  int nextFrameIdx = 0;
  PlayExit outcome = PlayExit::MENU;
  bool backArmed = false;
  bool backPrevHeld = false;
  const uint32_t playbackStartMs = millis();
  g_videoTrackNavRequest = 0;

  for (;;) {
    if (!playing) {
      M5Cardputer.update();
      M5Cardputer.Keyboard.updateKeysState();
      const bool keyChanged = M5Cardputer.Keyboard.isChange();
      if (systemInfoOverlayActive()) {
        if (pcmOpen) {
          M5Cardputer.Speaker.stop();
        }
        drawSystemInfoScreen();
        delay(20);
        continue;
      }
      PlayKey pk = pollPlaybackKeys(keyChanged, backArmed, backPrevHeld, playbackStartMs);
      pk = augmentPlayKeyWithVideoSeekRaw(pk);
      if (pk == PlayKey::NONE || pk == PlayKey::SEEK_LEFT || pk == PlayKey::SEEK_RIGHT) {
        const PlayKey fk = pollMjpegSeekFromPressFifo();
        if (fk != PlayKey::NONE) {
          pk = fk;
        }
      }
      if (pk == PlayKey::BACK_MENU) {
        outcome = PlayExit::MENU;
        break;
      }
      if (pk == PlayKey::PAUSE_TOGGLE) {
        playing = true;
      }
      if (pk == PlayKey::TOGGLE_LOOP) {
        g_loopEnabled = !g_loopEnabled;
        Serial.printf("Loop %s\n", g_loopEnabled ? "ON" : "OFF");
        showLoopHintNow();
      }
      if (pk == PlayKey::TOGGLE_AUTOPLAY) {
        g_folderAutoplay = !g_folderAutoplay;
        Serial.printf("Folder autoplay %s\n", g_folderAutoplay ? "ON" : "OFF");
      }
      if (pk == PlayKey::SEEK_RIGHT) {
        applySeekForward(v, pcmFile, pcmOpen, nextFrameIdx);
        displayOneFrameAfterSeek(v, nextFrameIdx);
      } else if (pk == PlayKey::SEEK_LEFT) {
        if (applySeekBack(videoPath, pcmPath, v, pcmFile, pcmOpen, nextFrameIdx)) {
          displayOneFrameAfterSeek(v, nextFrameIdx);
        }
      } else if (pk == PlayKey::TRACK_NEXT) {
        outcome = PlayExit::TRACK_NEXT;
        break;
      } else if (pk == PlayKey::TRACK_PREV) {
        outcome = PlayExit::TRACK_PREV;
        break;
      }
      if (pk == PlayKey::S_SET_MEDIA) {
        g_sSetMediaPath = videoPath;
        showSetBookmarkHintNow();
      }
      if (pk == PlayKey::SHOW_KEYS_HINT) {
        keysHintOnHKey(nullptr);
      }
      drawMp3LoopHintTick();
      drawSetBookmarkHintTick();
      drawMp3VolumeHintTick();
      drawKeysHintOverlayTick(nullptr);
      if (g_keysHintNeedFullUiRedraw) {
        g_keysHintNeedFullUiRedraw = false;
        g_mjpeg.drawJpg();
      }
      delay(20);
      continue;
    }

    uint32_t tFrame = millis();
    // Video path does heavy SD read + JPEG decode/draw before `waitFramePace()`.
    // That can delay keyboard polling enough to miss fast volume taps.
    // Poll volume here once per outer loop iteration so `-/_` and `=+` feel closer
    // to the MP3 path responsiveness.
    M5Cardputer.update();
    M5Cardputer.Keyboard.updateKeysState();
    pollVolumeKeysMatrix(nullptr);
    const PlayKey nb = pollTrackNavNextPrev();
    if (nb == PlayKey::TRACK_NEXT || nb == PlayKey::TRACK_PREV) {
      outcome = (nb == PlayKey::TRACK_NEXT) ? PlayExit::TRACK_NEXT : PlayExit::TRACK_PREV;
      break;
    }

    if (g_keysHintNeedFullUiRedraw) {
      g_keysHintNeedFullUiRedraw = false;
      g_mjpeg.drawJpg();
    }

    bool fedSpeaker = false;
    if (pcmOpen && pcmFile.available()) {
      const size_t n = pcmFile.read(g_audioBuf, AUDIO_CHUNK);
      if (n == 0) {
        pcmOpen = false;
        pcmFile.close();
      } else {
        if (n < AUDIO_CHUNK) {
          memset(g_audioBuf + n, 128, AUDIO_CHUNK - n);
        }
        M5Cardputer.Speaker.playRaw(g_audioBuf, AUDIO_CHUNK, AUDIO_RATE, false);
        fedSpeaker = true;
      }
    }

    bool got = false;
    while (v.available()) {
      if (g_mjpeg.readMjpegBuf()) {
        got = true;
        break;
      }
    }
    if (!got) {
      Serial.println("End of stream");
      if (g_loopEnabled) {
        M5Cardputer.Speaker.stop();
        g_mjpeg.reset();
        v.close();
        if (pcmOpen) {
          pcmFile.close();
          pcmOpen = false;
        }
        v = SD.open(videoPath.c_str(), FILE_READ);
        if (!v || v.isDirectory()) {
          outcome = PlayExit::MENU;
          break;
        }
        g_mjpeg.setup(v, g_mjpegBuf, &M5Cardputer.Display, false);
        nextFrameIdx = 0;
        if (SD.exists(pcmPath.c_str())) {
          pcmFile = SD.open(pcmPath.c_str(), FILE_READ);
          if (pcmFile && !pcmFile.isDirectory() && pcmFile.size() > 0) {
            pcmOpen = true;
            pcmFile.seek(0);
          } else {
            if (pcmFile) {
              pcmFile.close();
            }
          }
        }
        playing = true;
        continue;
      }
      outcome = PlayExit::TRACK_FINISHED;
      break;
    }

    g_mjpeg.drawJpg();
    drawMp3LoopHintTick();
    drawSetBookmarkHintTick();
    drawMp3VolumeHintTick();
    drawKeysHintOverlayTick(nullptr);
    nextFrameIdx++;

    if (!waitFramePace(fedSpeaker, playing, tFrame, videoPath, pcmPath, v, pcmFile, pcmOpen,
                       nextFrameIdx, backArmed, backPrevHeld, playbackStartMs)) {
      if (g_videoTrackNavRequest > 0) {
        outcome = PlayExit::TRACK_NEXT;
      } else if (g_videoTrackNavRequest < 0) {
        outcome = PlayExit::TRACK_PREV;
      } else {
        outcome = PlayExit::MENU;
      }
      g_videoTrackNavRequest = 0;
      break;
    }
  }

  M5Cardputer.Speaker.stop();
  if (pcmOpen) {
    pcmFile.close();
  }
  v.close();
  g_mjpeg.reset();
  markPlaybackReturnedToMenu();
  return outcome;
}

static PlayKey mp3PollAllKeys(AudioOutputI2S *out, Mp3VizMode &vizMode, bool &duckStaticNeedsRedraw,
                              bool &tapeStillNeedsRedraw, bool keyChanged, uint32_t &lastPauseToggleMs,
                              bool &backArmed, bool &backPrevHeld, uint32_t playbackStartMs) {
  const auto &st = M5Cardputer.Keyboard.keysState();
  const auto &pes = M5Cardputer.Keyboard.pressEvents();
  const bool btnAClick = M5Cardputer.BtnA.wasClicked();

  // MP3 pause: st.word *press* edges only — matrix/HID often ghosts `p` when `v` is pressed on ADV.
  static bool s_prevWordHadP = false;
  static bool s_prevWordHadV = false;
  bool wordHasP = false;
  bool wordHasV = false;
  for (char c : st.word) {
    if (c == 'p' || c == 'P') {
      wordHasP = true;
    }
    if (c == 'v' || c == 'V') {
      wordHasV = true;
    }
  }
  const bool wordPEdge = wordHasP && !s_prevWordHadP;
  const bool wordVEdge = wordHasV && !s_prevWordHadV;
  s_prevWordHadP = wordHasP;
  s_prevWordHadV = wordHasV;

  // Physical `p` rising edge — repeats every tap even when st.word sticks between releases.
  static bool s_prevPHeldDriver = false;
  const bool pHeldDriver =
      M5Cardputer.Keyboard.isKeyPressed('p') || M5Cardputer.Keyboard.isKeyPressed('P');
  const bool pDriverEdge = pHeldDriver && !s_prevPHeldDriver;
  s_prevPHeldDriver = pHeldDriver;

  if (playbackBackEdge(st, backArmed, backPrevHeld, playbackStartMs)) {
    return PlayKey::BACK_MENU;
  }

  pollVolumeKeysMatrix(out);

  const bool hHeldStrictM = playbackKeysHintHHeldStrictNow();
  const bool enterBlocksHintM = enterHeldNow(st) || enterPressedEdgeNow();
  if (hHeldStrictM && !g_mp3PollHPrev && !enterBlocksHintM) {
    g_mp3PollHPrev = true;
    return PlayKey::SHOW_KEYS_HINT;
  }
  if (!hHeldStrictM) {
    g_mp3PollHPrev = false;
  }

  const PlayKey nb = pollTrackNavNextPrev();
  if (nb == PlayKey::TRACK_NEXT || nb == PlayKey::TRACK_PREV) {
    return nb;
  }

  const uint32_t now = millis();
  const auto hasAnyNonModifierHeld = [&]() -> bool {
    for (const Point2D_t &k : M5Cardputer.Keyboard.keyList()) {
      const uint8_t base = static_cast<uint8_t>(M5Cardputer.Keyboard.getKeyValue(k).value_first);
      if (base == KEY_FN || base == KEY_OPT || base == KEY_LEFT_CTRL || base == KEY_LEFT_SHIFT ||
          base == KEY_LEFT_ALT) {
        continue;
      }
      return true;
    }
    return false;
  };

  if (btnAClick && pes.empty() && !hasAnyNonModifierHeld() &&
      static_cast<int32_t>(now - g_ignorePauseToggleUntilMs) >= 0 &&
      now - lastPauseToggleMs >= kMp3PauseToggleDebounceMs) {
    return PlayKey::PAUSE_TOGGLE;
  }

  auto pressEventDecodesV = [&](const Point2D_t &pe) -> bool {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(pe);
    const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(pe);
    return kch == static_cast<uint8_t>('v') || kch == static_cast<uint8_t>('V') ||
           kv.value_first == 'v' || kv.value_second == 'V';
  };

  bool pesHasV = false;
  for (const Point2D_t &pe : pes) {
    if (pressEventDecodesV(pe)) {
      pesHasV = true;
      break;
    }
  }

  const bool vHeldDriver =
      M5Cardputer.Keyboard.isKeyPressed('v') || M5Cardputer.Keyboard.isKeyPressed('V');

  // Pause before viz. Do not require !vHeldDriver here — isKeyPressed('v') can stick after `v`
  // taps and would block pause forever; physical `p` edge is the intentional action.
  if (pDriverEdge && static_cast<int32_t>(now - g_ignoreVizToggleUntilMs) >= 0 &&
      static_cast<int32_t>(now - g_ignorePauseToggleUntilMs) >= 0 &&
      now - lastPauseToggleMs >= kMp3PauseToggleDebounceMs) {
    g_ignoreVizToggleUntilMs = now + 180u;
    return PlayKey::PAUSE_TOGGLE;
  }
  if (keyChanged && wordPEdge && !wordHasV && !vHeldDriver && !pesHasV &&
      static_cast<int32_t>(now - g_ignoreVizToggleUntilMs) >= 0 &&
      static_cast<int32_t>(now - g_ignorePauseToggleUntilMs) >= 0 &&
      now - lastPauseToggleMs >= kMp3PauseToggleDebounceMs) {
    g_ignoreVizToggleUntilMs = now + 180u;
    return PlayKey::PAUSE_TOGGLE;
  }

  const bool vWant = pesHasV || (keyChanged && wordVEdge);

  static constexpr Mp3VizMode kMp3VizCycleOrder[] = {Mp3VizMode::TAPE_STILL,
                                                       Mp3VizMode::BARS,
                                                       Mp3VizMode::MATRIX,
                                                       Mp3VizMode::WAVE,
                                                       Mp3VizMode::DUCK_STILL,
                                                       Mp3VizMode::DUCK_DANCE};
  static constexpr uint8_t kMp3VizCycleOrderCount =
      sizeof(kMp3VizCycleOrder) / sizeof(kMp3VizCycleOrder[0]);
  auto cycleMp3VizMode = [&]() {
    for (uint8_t i = 0; i < kMp3VizCycleOrderCount; ++i) {
      if (vizMode == kMp3VizCycleOrder[i]) {
        vizMode = kMp3VizCycleOrder[(i + 1u) % kMp3VizCycleOrderCount];
        break;
      }
    }
    duckStaticNeedsRedraw = (vizMode == Mp3VizMode::DUCK_STILL);
    tapeStillNeedsRedraw = (vizMode == Mp3VizMode::TAPE_STILL);
  };

  if (vWant && static_cast<int32_t>(now - g_ignoreVizToggleUntilMs) >= 0) {
    g_ignoreVizToggleUntilMs = now + 40u;
    if (now - g_lastVizToggleMs >= kMp3VizToggleDebounceMs) {
      g_lastVizToggleMs = now;
      cycleMp3VizMode();
      g_ignorePauseToggleUntilMs = now + 140u;
    } else {
      g_ignorePauseToggleUntilMs = now + 90u;
    }
    return PlayKey::NONE;
  }

  const bool sDownM = menuLetterDownWithFifo('s', 'S');
  if (sDownM && !g_mp3PollSPrev) {
    g_mp3PollSPrev = true;
    return PlayKey::S_SET_MEDIA;
  }
  if (!sDownM) {
    g_mp3PollSPrev = false;
  }

  if (!keyChanged) {
    return PlayKey::NONE;
  }

  if (vizMode == Mp3VizMode::MATRIX) {
    if (hidHas(st.hid_keys, HID_UP)) {
      // Shorter interval = faster rain
      g_mp3MatrixStepIntervalMs =
          static_cast<uint16_t>(constrain(static_cast<int>(g_mp3MatrixStepIntervalMs) - 18, 22, 480));
      return PlayKey::NONE;
    }
    if (hidHas(st.hid_keys, HID_DOWN)) {
      g_mp3MatrixStepIntervalMs =
          static_cast<uint16_t>(constrain(static_cast<int>(g_mp3MatrixStepIntervalMs) + 18, 22, 480));
      return PlayKey::NONE;
    }
  }
  for (char c : st.word) {
    if (c == ',') {
      return PlayKey::SEEK_LEFT;
    }
    if (c == '/') {
      return PlayKey::SEEK_RIGHT;
    }
  }

  // Prioritize loop/autoplay toggles over viz-cycle to avoid ghosting-triggered V changes.
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    if (kch == static_cast<uint8_t>('l') || kch == static_cast<uint8_t>('L')) {
      return PlayKey::TOGGLE_LOOP;
    }
    if (kch == static_cast<uint8_t>('a') || kch == static_cast<uint8_t>('A')) {
      return PlayKey::TOGGLE_AUTOPLAY;
    }
  }
  for (char c : st.word) {
    if (c == 'l' || c == 'L') {
      return PlayKey::TOGGLE_LOOP;
    }
    if (c == 'a' || c == 'A') {
      return PlayKey::TOGGLE_AUTOPLAY;
    }
  }

  return PlayKey::NONE;
}

// Still tape art in MP3 viz band — same SD path order as startup splash (magnetic1 first); else embedded PNG.
static void drawMp3TapeStillViz() {
  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizH = yBot - yTop + 1;
  const int vizW = d.width();
  if (vizH < 8 || vizW < 8) {
    return;
  }
  d.fillRect(0, yTop, vizW, vizH, TFT_BLACK);
  d.setClipRect(0, yTop, vizW, vizH);
  // Important: draw from embedded PNG for performance.
  // Re-decoding from SD on every return to this viz can cause audio underruns ("music skip").
  int32_t picW = 0;
  int32_t picH = 0;
  if (splashReadPngIhdr(kTapeOMagnetic1SplashPng, kTapeOMagnetic1SplashPngLen, picW, picH)) {
#if defined(ESP_PLATFORM)
    yield();
#endif
    float zx = 1.0f;
    float zy = 1.0f;
    int lx = 0;
    int ly = 0;
    tapeStretchToFillZooms(vizW, vizH, picW, picH, zx, zy, lx, ly);
    const uint32_t splashLen = static_cast<uint32_t>(kTapeOMagnetic1SplashPngLen);
    (void)d.drawPng(kTapeOMagnetic1SplashPng, splashLen, lx, ly + yTop, 0, 0, 0, 0, zx, zy,
                    lgfx::datum_t::top_left);
  }
  d.setClipRect(0, 0, d.width(), d.height());
}

static void drawMp3DuckVisualizerArea() {
  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizH = yBot - yTop + 1;
  const int vizW = d.width();
  if (vizH < 8 || vizW < 8) {
    return;
  }
  d.fillRect(0, yTop, vizW, vizH, TFT_BLACK);
  const int ix = (vizW - SPLASH_DUCK_W) / 2;
  const int iy = yTop + (vizH - SPLASH_DUCK_H) / 2;
  d.pushImage(ix, iy, SPLASH_DUCK_W, SPLASH_DUCK_H, SPLASH_DUCK_RGB565);
}

// Duck moves with audio envelope (hop + sway) plus a continuous waddle; redraws every frame.
static void drawMp3DancingDuckTick(bool paused, volatile uint32_t *envPtr) {
  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizH = yBot - yTop + 1;
  const int vizW = d.width();
  if (vizH < SPLASH_DUCK_H + 4 || vizW < SPLASH_DUCK_W + 4) {
    return;
  }

  uint32_t env = envPtr ? *envPtr : 0u;
  if (paused) {
    env = env * 2 / 5;
  }

  d.fillRect(0, yTop, vizW, vizH, TFT_BLACK);

  const int baseCx = vizW / 2;
  const int baseCy = yTop + vizH / 2;
  const uint32_t t = millis();
  const float ft = static_cast<float>(t) * 0.0011f;
  const float twoPi = 6.2831853f;

  const int hop = constrain(static_cast<int>(env * 22u / 20000u), 0, 22);
  const float waddle = sinf(ft * twoPi) * 11.0f + sinf(ft * twoPi * 2.0f) * 5.0f;
  const int beatPush = constrain(static_cast<int>(env) / 2200 - 3, -8, 10);
  const int idleBob = static_cast<int>(sinf(ft * twoPi * 2.7f) * 3.0f);

  int ix = baseCx - SPLASH_DUCK_W / 2 + static_cast<int>(waddle) + beatPush + idleBob;
  int iy = baseCy - SPLASH_DUCK_H / 2 - hop;

  ix = constrain(ix, 1, vizW - SPLASH_DUCK_W - 1);
  iy = constrain(iy, yTop + 1, yBot - SPLASH_DUCK_H - 1);

  d.pushImage(ix, iy, SPLASH_DUCK_W, SPLASH_DUCK_H, SPLASH_DUCK_RGB565);
}

// --- MP3 "dance" viz: AnimatedGIF from SD, center-cropped on canvas, placed like the static duck; fallback = procedural duck above.
static AnimatedGIF g_mp3Gif;
static File g_mp3GifSdFile;
static bool g_mp3GifIsOpen = false;
static bool g_mp3GifUseFallback = false;
// GIF logical canvas crop (source pixels), then mapped to screen with bases below.
static int g_mp3GifCropX = 0;
static int g_mp3GifCropY = 0;
static int g_mp3GifCropW = 0;
static int g_mp3GifCropH = 0;
static int g_mp3GifScrBaseX = 0;
static int g_mp3GifScrBaseY = 0;
static int g_mp3GifVisTop = 0;
static int g_mp3GifVisBot = 0;
static uint32_t g_mp3GifNextFrameMs = 0;

// How much of the GIF width/height to keep from the center (100 = full frame).
static constexpr int kMp3DanceGifCropPercent = 55;

static const char *const kMp3DanceGifPaths[] = {
    "/dancing-duck-colorful-happy-duck.gif",
    "/mp3_duck.gif",
    "/dance_duck.gif",
    "/duck_dance.gif",
};
static constexpr int kMp3DanceGifPathCount = sizeof(kMp3DanceGifPaths) / sizeof(kMp3DanceGifPaths[0]);

static void mp3GifSetCenterCrop(int cw, int ch, int vizW, int vizH, int yTop) {
  int cropW = cw * kMp3DanceGifCropPercent / 100;
  int cropH = ch * kMp3DanceGifCropPercent / 100;
  if (cropW < 1) {
    cropW = 1;
  }
  if (cropH < 1) {
    cropH = 1;
  }
  if (cropW > cw) {
    cropW = cw;
  }
  if (cropH > ch) {
    cropH = ch;
  }
  g_mp3GifCropX = (cw - cropW) / 2;
  g_mp3GifCropY = (ch - cropH) / 2;
  g_mp3GifCropW = cropW;
  g_mp3GifCropH = cropH;
  g_mp3GifScrBaseX = (vizW - cropW) / 2;
  g_mp3GifScrBaseY = yTop + (vizH - cropH) / 2;
}

static void mp3GifPushLine(int canvasX, int canvasY, int w, uint16_t *buf) {
  if (w <= 0) {
    return;
  }
  if (canvasY < g_mp3GifCropY || canvasY >= g_mp3GifCropY + g_mp3GifCropH) {
    return;
  }
  const int sy = g_mp3GifScrBaseY + (canvasY - g_mp3GifCropY);
  if (sy < g_mp3GifVisTop || sy > g_mp3GifVisBot) {
    return;
  }
  const int lineL = canvasX;
  const int lineR = canvasX + w;
  const int cropL = g_mp3GifCropX;
  const int cropR = g_mp3GifCropX + g_mp3GifCropW;
  const int segL = (lineL > cropL) ? lineL : cropL;
  const int segR = (lineR < cropR) ? lineR : cropR;
  if (segR <= segL) {
    return;
  }
  const int bufSkip = segL - lineL;
  const int runW = segR - segL;
  int sx = g_mp3GifScrBaseX + (segL - g_mp3GifCropX);

  auto &d = M5Cardputer.Display;
  const int dw = d.width();
  int clipL = 0;
  if (sx < 0) {
    clipL = -sx;
    sx = 0;
  }
  int drawW = runW - clipL;
  if (drawW <= 0) {
    return;
  }
  if (sx + drawW > dw) {
    drawW = dw - sx;
  }
  if (drawW <= 0) {
    return;
  }
  d.pushImage(sx, sy, drawW, 1, buf + bufSkip + clipL);
}

static void mp3GifDrawCb(GIFDRAW *pDraw) {
  uint8_t *s;
  uint16_t *dPtr;
  uint16_t *usPalette;
  uint16_t usTemp[480];
  int x;
  int y;
  int iWidth = pDraw->iWidth;
  if (iWidth > 480) {
    iWidth = 480;
  }
  usPalette = pDraw->pPalette;
  y = pDraw->iY + pDraw->y;
  s = pDraw->pPixels;
  if (pDraw->ucDisposalMethod == 2) {
    for (x = 0; x < iWidth; x++) {
      if (s[x] == pDraw->ucTransparent) {
        s[x] = pDraw->ucBackground;
      }
    }
    pDraw->ucHasTransparency = 0;
  }
  if (pDraw->ucHasTransparency) {
    uint8_t *pEnd;
    uint8_t c;
    uint8_t ucTransparent = pDraw->ucTransparent;
    pEnd = s + iWidth;
    x = 0;
    while (x < iWidth) {
      c = static_cast<uint8_t>(ucTransparent - 1u);
      dPtr = usTemp;
      int iCount = 0;
      while (c != ucTransparent && s < pEnd) {
        c = *s++;
        if (c == ucTransparent) {
          s--;
        } else {
          *dPtr++ = usPalette[c];
          iCount++;
        }
      }
      if (iCount) {
        mp3GifPushLine(pDraw->iX + x, y, iCount, usTemp);
        x += iCount;
      }
      c = ucTransparent;
      iCount = 0;
      while (c == ucTransparent && s < pEnd) {
        c = *s++;
        if (c == ucTransparent) {
          iCount++;
        } else {
          s--;
        }
      }
      if (iCount) {
        x += iCount;
      }
    }
  } else {
    s = pDraw->pPixels;
    for (x = 0; x < iWidth; x++) {
      usTemp[x] = usPalette[*s++];
    }
    mp3GifPushLine(pDraw->iX, y, iWidth, usTemp);
  }
}

static void *mp3GifOpenFile(const char *fname, int32_t *pSize) {
  g_mp3GifSdFile = SD.open(fname);
  if (!g_mp3GifSdFile) {
    return nullptr;
  }
  *pSize = static_cast<int32_t>(g_mp3GifSdFile.size());
  return static_cast<void *>(&g_mp3GifSdFile);
}

static void mp3GifCloseFile(void *pHandle) {
  (void)pHandle;
  g_mp3GifSdFile.close();
}

static int32_t mp3GifReadFile(GIFFILE *pFile, uint8_t *pBuf, int32_t iLen) {
  auto *f = static_cast<File *>(pFile->fHandle);
  int32_t iBytesRead = iLen;
  if ((pFile->iSize - pFile->iPos) < iLen) {
    iBytesRead = pFile->iSize - pFile->iPos - 1;
  }
  if (iBytesRead <= 0) {
    return 0;
  }
  iBytesRead = static_cast<int32_t>(f->read(pBuf, static_cast<size_t>(iBytesRead)));
  pFile->iPos = static_cast<int32_t>(f->position());
  return iBytesRead;
}

static int32_t mp3GifSeekFile(GIFFILE *pFile, int32_t iPosition) {
  auto *f = static_cast<File *>(pFile->fHandle);
  f->seek(iPosition);
  pFile->iPos = static_cast<int32_t>(f->position());
  return pFile->iPos;
}

static void mp3GifClose() {
  if (g_mp3GifIsOpen) {
    g_mp3Gif.close();
    g_mp3GifIsOpen = false;
  }
}

static bool mp3GifTryOpenForDanceViz() {
  mp3GifClose();
  g_mp3GifUseFallback = false;

  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizW = d.width();
  const int vizH = yBot - yTop + 1;
  d.fillRect(0, yTop, vizW, vizH, TFT_BLACK);

  g_mp3GifVisTop = yTop;
  g_mp3GifVisBot = yBot;

  for (int i = 0; i < kMp3DanceGifPathCount; i++) {
    // Little-endian RGB565 matches typical M5GFX pushImage; use begin(BIG_ENDIAN_PIXELS) if colors look wrong.
    g_mp3Gif.begin(LITTLE_ENDIAN_PIXELS);
    if (!g_mp3Gif.open(kMp3DanceGifPaths[i], mp3GifOpenFile, mp3GifCloseFile, mp3GifReadFile, mp3GifSeekFile,
                       mp3GifDrawCb)) {
      continue;
    }
    const int cw = g_mp3Gif.getCanvasWidth();
    const int ch = g_mp3Gif.getCanvasHeight();
    if (cw < 1 || ch < 1) {
      g_mp3Gif.close();
      continue;
    }
    mp3GifSetCenterCrop(cw, ch, vizW, vizH, yTop);
    g_mp3GifIsOpen = true;
    int dly = 33;
    const int rc = g_mp3Gif.playFrame(false, &dly);
    if (dly < 1) {
      dly = 1;
    }
    g_mp3GifNextFrameMs = millis() + static_cast<uint32_t>(dly);
    if (rc < 0) {
      mp3GifClose();
      g_mp3GifUseFallback = true;
      return false;
    }
    return true;
  }
  g_mp3GifUseFallback = true;
  return false;
}

static void mp3GifDanceVizTick(bool paused, volatile uint32_t *envPtr) {
  if (g_mp3GifUseFallback || !g_mp3GifIsOpen) {
    drawMp3DancingDuckTick(paused, envPtr);
    return;
  }
  if (paused) {
    return;
  }
  const uint32_t now = millis();
  if (static_cast<int32_t>(now - g_mp3GifNextFrameMs) < 0) {
    return;
  }
  int dly = 33;
  const int rc = g_mp3Gif.playFrame(false, &dly);
  if (dly < 1) {
    dly = 1;
  }
  g_mp3GifNextFrameMs = now + static_cast<uint32_t>(dly);
  if (rc < 0) {
    g_mp3GifUseFallback = true;
    mp3GifClose();
    drawMp3DancingDuckTick(paused, envPtr);
  }
}

// Bar heights follow I2S sample envelope (see AudioOutputMeterI2S).
static void drawMp3VisualizerTick(bool paused, volatile uint32_t *envPtr) {
  auto &d = M5Cardputer.Display;
  const int nx = 14;
  const int barW = 14;
  const int gap = 2;
  const int x0 = 5;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int maxH = yBot - yTop;
  if (maxH < 12) {
    return;
  }

  uint32_t env = envPtr ? *envPtr : 0u;
  if (paused) {
    env = env * 2 / 5;
  }
  const int base = constrain(static_cast<int>(env * static_cast<uint32_t>(maxH) / 20000u), 3, maxH);

  d.fillRect(0, yTop, d.width(), yBot - yTop + 1, TFT_BLACK);
  static const uint16_t cols[] = {TFT_CYAN, TFT_GREEN, TFT_MAGENTA, TFT_YELLOW};
  const uint32_t t = millis();
  for (int i = 0; i < nx; i++) {
    const float phase = static_cast<float>(i * 23 + static_cast<int>(t / 70)) * 0.14f;
    float w = 0.38f + 0.62f * (0.5f + 0.5f * sinf(phase));
    if (w < 0.12f) {
      w = 0.12f;
    }
    int h = static_cast<int>(static_cast<float>(base) * w);
    h = constrain(h, 2, maxH);
    const int x = x0 + i * (barW + gap);
    d.fillRect(x, yBot - h, barW, h, cols[i & 3]);
  }
}

#if defined(ESP_PLATFORM)
static uint32_t mp3VizRand32() {
  return esp_random();
}
#else
static uint32_t mp3VizRand32() {
  return static_cast<uint32_t>(random(0x7fffffff));
}
#endif

// Matrix rain: with Display rotation 1 on Cardputer ADV, logical X matches the long side users see as “top→bottom”
// of the MP3 band; logical Y reads as left↔right. Fall runs along X; streams are spaced on Y.
// Whole segment spawns before the band on the fall axis, traverses, exits past the far end, then a gap.
static constexpr int kMatrixMaxRows = 32;
static constexpr int kMatrixMaxStreams = 40;
static constexpr int kMatrixMaxTrail = 22;
static int g_mx_headRow[kMatrixMaxStreams];  // cell index along fall axis (0 = start of band); ++ → toward “bottom”
static int g_mx_tailLen[kMatrixMaxStreams];
static char g_mx_trailC[kMatrixMaxStreams][kMatrixMaxTrail];
static int g_mx_R = 0;
static int g_mx_nStreams = 0;
static int g_mx_fallPitch = 0;   // pixels per cell along fall (logical X on ADV rot 1)
static int g_mx_streamPitch = 0; // pixels between streams on logical Y
static int g_mx_vizH = 0;
static int g_mx_vizW = 0;
static int g_mx_cellW = 0;
static int g_mx_cellH = 0;

static inline char matrixRandomPrintableAsciiChar() {
  return static_cast<char>(33 + (mp3VizRand32() % 94u));
}

static int matrixRandomGapTicks(int R) {
  const uint32_t span = static_cast<uint32_t>(std::max(R, 8));
  return 4 + static_cast<int>(mp3VizRand32() % (span * 2u / 3u + 6u));
}

static void matrixSpawnStream(int dc, int R) {
  const int cap = std::min(kMatrixMaxTrail, std::max(4, (R * 2) / 3));
  int tl = 3 + static_cast<int>(mp3VizRand32() % static_cast<uint32_t>(std::max(2, cap - 2)));
  if (tl > kMatrixMaxTrail) {
    tl = kMatrixMaxTrail;
  }
  g_mx_tailLen[dc] = tl;
  const int gap = matrixRandomGapTicks(R);
  g_mx_headRow[dc] = -(tl + gap);
  for (int i = 0; i < tl; i++) {
    g_mx_trailC[dc][i] = matrixRandomPrintableAsciiChar();
  }
  if ((mp3VizRand32() % 4u) == 0u) {
    g_mx_trailC[dc][0] = '&';
  }
}

static void matrixStreamsInitAll(int R, int nStreams) {
  for (int dc = 0; dc < nStreams; dc++) {
    matrixSpawnStream(dc, R);
    g_mx_headRow[dc] += static_cast<int>(mp3VizRand32() % static_cast<uint32_t>(R + 24));
    g_mx_headRow[dc] -= dc * 2;
  }
}

static void drawMp3MatrixRainTick(bool paused, volatile uint32_t *envPtr) {
  (void)envPtr;
  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizH = yBot - yTop + 1;
  const int vizW = d.width();
  d.setTextSize(1);
  int cellW = static_cast<int>(d.fontWidth());
  int cellH = static_cast<int>(d.fontHeight());
  if (cellW < 4) {
    cellW = 6;
  }
  if (cellH < 4) {
    cellH = 8;
  }
  int glyphW = static_cast<int>(d.textWidth("M"));
  if (glyphW < cellW) {
    glyphW = cellW;
  }
  if (glyphW < 6) {
    glyphW = 6;
  }
  const int glyphH = cellH;
  constexpr int kMxMarginX = 2;
  const int bandW = vizW - kMxMarginX * 2;
  if (bandW < 16 || vizH < glyphH + 10) {
    return;
  }

  const int fallPitchX = std::max(glyphW, 6);
  int R = bandW / std::max(fallPitchX, 1);
  if (R < 2) {
    return;
  }
  if (R > kMatrixMaxRows) {
    R = kMatrixMaxRows;
  }
  const int usedFallW = R * fallPitchX;
  const int xStart = kMxMarginX + std::max(0, (bandW - usedFallW) / 2);

  const int streamPitchY = std::max(glyphH + 2, 9);
  int nStreams = vizH / std::max(streamPitchY, 1);
  if (nStreams < 2) {
    return;
  }
  nStreams = std::min(kMatrixMaxStreams, std::max(3, nStreams));
  const int usedStreamH = nStreams * streamPitchY;
  const int yRain0 = yTop + std::max(0, (vizH - usedStreamH) / 2);

  if (g_mx_R != R || g_mx_nStreams != nStreams || g_mx_fallPitch != fallPitchX ||
      g_mx_streamPitch != streamPitchY || g_mx_vizH != vizH || g_mx_vizW != vizW || g_mx_cellW != cellW ||
      g_mx_cellH != cellH) {
    g_mx_R = R;
    g_mx_nStreams = nStreams;
    g_mx_fallPitch = fallPitchX;
    g_mx_streamPitch = streamPitchY;
    g_mx_vizH = vizH;
    g_mx_vizW = vizW;
    g_mx_cellW = cellW;
    g_mx_cellH = cellH;
    matrixStreamsInitAll(R, nStreams);
  }

  const uint32_t now = millis();
  const bool canAdvance =
      !paused &&
      (g_mp3MatrixLastAdvanceMs == 0u ||
       static_cast<int32_t>(now - g_mp3MatrixLastAdvanceMs) >= static_cast<int32_t>(g_mp3MatrixStepIntervalMs));
  if (!canAdvance) {
    return;
  }
  g_mp3MatrixLastAdvanceMs = now;

  for (int dc = 0; dc < nStreams; dc++) {
    g_mx_headRow[dc]++;
    const int L = g_mx_tailLen[dc];
    const int tailBack = g_mx_headRow[dc] - (L - 1);
    if (tailBack > R - 1) {
      matrixSpawnStream(dc, R);
    }
  }

  // Clear from the MP3 band top down to the bottom of the screen.
  // The ASCII glyph renderer can draw a few pixels past our computed band edge,
  // which otherwise causes "lingering" characters after switching visuals.
  d.fillRect(0, yTop, vizW, d.height() - yTop, TFT_BLACK);
  d.setTextDatum(textdatum_t::top_left);

  for (int dc = 0; dc < nStreams; dc++) {
    const int L = g_mx_tailLen[dc];
    const int py = yRain0 + dc * streamPitchY;
    if (py + glyphH > yBot + 1) {
      continue;
    }
    for (int i = 0; i < L; i++) {
      const int row = g_mx_headRow[dc] - i;
      if (row < 0 || row >= R) {
        continue;
      }
      const int px = xStart + row * fallPitchX;
      if (px + glyphW > vizW - kMxMarginX) {
        continue;
      }
      const char drawCh = g_mx_trailC[dc][i];
      uint16_t fg;
      if (i == 0) {
        fg = TFT_WHITE;
      } else if (i < 3) {
        fg = 0xAFE5;
      } else if (i < 6) {
        fg = 0x07E0;
      } else {
        fg = 0x0320;
      }
      d.setTextColor(fg, TFT_BLACK);
      d.drawChar(px, py, drawCh);
    }
  }
}

// Simple oscilloscope-style wave visual (5th mode).
// Clears the full MP3 band every frame to avoid lingering pixels.
static void drawMp3WaveTick(bool paused, volatile uint32_t *envPtr) {
  auto &d = M5Cardputer.Display;
  const int yTop = MP3_VIS_TOP;
  const int yBot = d.height() - MP3_VIS_BOTTOM_MARGIN;
  const int vizH = yBot - yTop + 1;
  const int vizW = d.width();
  if (vizH < 10 || vizW < 20) {
    return;
  }

  uint32_t env = envPtr ? *envPtr : 0u;
  if (paused) {
    env = env * 2 / 5;
  }

  // Map envelope (roughly 0..20000) to pixel amplitude.
  const int maxAmp = std::max(3, vizH / 3);
  const int amp = constrain(static_cast<int>(env * static_cast<uint32_t>(maxAmp) / 20000u), 0, maxAmp);

  d.fillRect(0, yTop, vizW, vizH, TFT_BLACK);
  const int midY = yTop + vizH / 2;

  const uint32_t t = millis();
  const float ft = static_cast<float>(t) * 0.006f;
  const float twoPi = 6.2831853f;

  // Draw a polyline with a step to reduce draw calls.
  const int xStep = 3;
  int prevX = 0;
  int prevY = midY;
  bool havePrev = false;
  for (int x = 0; x < vizW; x += xStep) {
    const float phase = ft + static_cast<float>(x) * 0.045f;
    const int y = midY + static_cast<int>(sinf(phase * 1.0f) * amp);
    if (y < yTop) {
      continue;
    }
    if (y > yBot) {
      continue;
    }
    if (havePrev) {
      // Gradient-ish color based on x.
      const uint16_t col = (x / xStep) & 1 ? 0x07E0 : 0xF81F;  // green/magenta
      d.drawLine(prevX, prevY, x, y, col);
    }
    prevX = x;
    prevY = y;
    havePrev = true;
  }
}

static void drawMp3ScreenStatic(const String &path) {
  auto &d = M5Cardputer.Display;
  d.fillScreen(TFT_BLACK);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  d.setTextSize(1);
  d.drawString("MP3", 4, 4);
  String title = displayBasename(path);
  if (title.length() > 26) {
    title = title.substring(0, 23) + "...";
  }
  d.drawString(title, 4, 18);
  d.setTextColor(TFT_DARKGREY, TFT_BLACK);
  // Bottom line only — avoids same row as elapsed/total (was easy to misread as "tap p u" when glitching).
  d.drawString("Tab P V ,/ seek N/B -+  mat U D spd", 2, d.height() - 11);
}

static void formatMp3MmSs(char *buf, size_t buflen, uint32_t sec) {
  const unsigned long m = static_cast<unsigned long>(sec / 60u);
  const unsigned long s = static_cast<unsigned long>(sec % 60u);
  snprintf(buf, buflen, "%lu:%02lu", m, s);
}

static uint32_t mp3ReadBE32(const uint8_t *p) {
  return (static_cast<uint32_t>(p[0]) << 24) | (static_cast<uint32_t>(p[1]) << 16) |
         (static_cast<uint32_t>(p[2]) << 8) | static_cast<uint32_t>(p[3]);
}

static uint32_t mp3Id3SyncSafe(const uint8_t *p) {
  return (static_cast<uint32_t>(p[0] & 0x7f) << 21) | (static_cast<uint32_t>(p[1] & 0x7f) << 14) |
         (static_cast<uint32_t>(p[2] & 0x7f) << 7) | static_cast<uint32_t>(p[3] & 0x7f);
}

static uint32_t probeMp3DurationId3Tlen(const uint8_t *buf, size_t len) {
  if (len < 10) {
    return 0;
  }
  if (buf[0] != 'I' || buf[1] != 'D' || buf[2] != '3') {
    return 0;
  }
  const uint8_t maj = buf[3];
  uint32_t tagsz = 0;
  if (maj == 4) {
    tagsz = mp3Id3SyncSafe(buf + 6);
  } else if (maj == 3) {
    tagsz = mp3ReadBE32(buf + 6);
  } else {
    return 0;
  }
  size_t pos = 10;
  const size_t tagEnd = 10 + static_cast<size_t>(tagsz);
  if (tagEnd > len) {
    return 0;
  }
  if ((buf[5] & 0x40) != 0) {
    if (pos + 4 > tagEnd) {
      return 0;
    }
    const uint32_t ex = mp3ReadBE32(buf + pos);
    pos += 4u + static_cast<size_t>(ex);
  }
  while (pos + 10 <= tagEnd) {
    if (buf[pos] == 0) {
      break;
    }
    char fid[5];
    memcpy(fid, buf + pos, 4);
    fid[4] = 0;
    uint32_t fsz = 0;
    if (maj == 4) {
      fsz = mp3Id3SyncSafe(buf + pos + 4);
    } else {
      fsz = mp3ReadBE32(buf + pos + 4);
    }
    pos += 10;
    if (pos + fsz > tagEnd) {
      break;
    }
    if (strcmp(fid, "TLEN") == 0 && fsz >= 2u) {
      uint64_t ms = 0;
      const size_t maxj = static_cast<size_t>(fsz) < 20u ? static_cast<size_t>(fsz) : 20u;
      for (size_t j = 1; j < maxj; j++) {
        const char c = static_cast<char>(buf[pos + j]);
        if (c >= '0' && c <= '9') {
          ms = ms * 10ull + static_cast<unsigned>(c - '0');
        }
      }
      if (ms >= 1000ull && ms < 864000000ull) {
        return static_cast<uint32_t>(ms / 1000ull);
      }
      return 0;
    }
    pos += static_cast<size_t>(fsz);
  }
  return 0;
}

static uint32_t probeMp3DurationXing(const uint8_t *buf, size_t len, size_t audioStart) {
  for (size_t i = audioStart; i + 16 < len; i++) {
    if (buf[i] != 0xff || (buf[i + 1] & 0xe0) != 0xe0) {
      continue;
    }
    const uint32_t h = mp3ReadBE32(buf + i);
    const unsigned ver = (h >> 19) & 3u;
    const unsigned layer = (h >> 17) & 3u;
    if (layer != 1u) {
      continue;
    }
    const unsigned srIdx = (h >> 10) & 3u;
    if (srIdx >= 3u) {
      continue;
    }
    static const uint16_t srMpeg1[3] = {44100, 48000, 32000};
    static const uint16_t srMpeg2[3] = {22050, 24000, 16000};
    static const uint16_t sr25[3] = {11025, 12000, 8000};
    unsigned sr = 44100;
    unsigned spf = 1152;
    if (ver == 3u) {
      sr = srMpeg1[srIdx];
      spf = 1152;
    } else if (ver == 2u) {
      sr = srMpeg2[srIdx];
      spf = 576;
    } else if (ver == 0u) {
      sr = sr25[srIdx];
      spf = 576;
    } else {
      continue;
    }
    const unsigned mode = (buf[i + 3] >> 6) & 3u;
    const unsigned side = (mode == 3u) ? 17u : 32u;
    const size_t x = i + 4u + static_cast<size_t>(side);
    if (x + 12 > len) {
      continue;
    }
    if (memcmp(buf + x, "Xing", 4) != 0 && memcmp(buf + x, "Info", 4) != 0) {
      continue;
    }
    const uint32_t flags = mp3ReadBE32(buf + x + 4);
    if ((flags & 1u) == 0) {
      continue;
    }
    const uint32_t nFrames = mp3ReadBE32(buf + x + 8);
    if (nFrames < 2u || nFrames > 2000000u) {
      continue;
    }
    const uint64_t samples = static_cast<uint64_t>(nFrames) * static_cast<uint64_t>(spf);
    return static_cast<uint32_t>((samples + sr / 2u) / static_cast<uint64_t>(sr));
  }
  return 0;
}

// Duration from ID3v2 TLEN (ms) or first MPEG frame Xing/Info frame count; 0 if unknown.
// Uses a temporary heap buffer (not 128KB static) so internal RAM stays available for speaker I2S + tasks.
static uint32_t probeMp3DurationSecSd(const char *path) {
  File f = SD.open(path, FILE_READ);
  if (!f || f.isDirectory()) {
    return 0;
  }
  const size_t sz = f.size();
  if (sz < 128) {
    f.close();
    return 0;
  }
  constexpr size_t kMaxProbe = 131072;
  const size_t chunk = sz < kMaxProbe ? sz : kMaxProbe;
#if defined(ESP_PLATFORM)
  uint8_t *buf = static_cast<uint8_t *>(heap_caps_malloc(chunk, MALLOC_CAP_8BIT));
#else
  uint8_t *buf = static_cast<uint8_t *>(malloc(chunk));
#endif
  if (!buf) {
    f.close();
    return 0;
  }
  const size_t nr = f.read(buf, chunk);
  f.close();
  if (nr < 128) {
#if defined(ESP_PLATFORM)
    heap_caps_free(buf);
#else
    free(buf);
#endif
    return 0;
  }
  size_t audioStart = 0;
  if (nr >= 10 && buf[0] == 'I' && buf[1] == 'D' && buf[2] == '3') {
    const uint8_t maj = buf[3];
    uint32_t tagsz = 0;
    if (maj == 4) {
      tagsz = mp3Id3SyncSafe(buf + 6);
    } else if (maj == 3) {
      tagsz = mp3ReadBE32(buf + 6);
    }
    audioStart = 10 + static_cast<size_t>(tagsz);
    if (audioStart > nr) {
      audioStart = nr;
    }
  }
  uint32_t d = probeMp3DurationId3Tlen(buf, nr);
  if (d == 0) {
    d = probeMp3DurationXing(buf, nr, audioStart);
  }
#if defined(ESP_PLATFORM)
  heap_caps_free(buf);
#else
  free(buf);
#endif
  if (d < 1u || d > 86400u) {
    return 0;
  }
  return d;
}

static void drawMp3PlaybackTimeTick(uint32_t playedMs, uint32_t totalSec) {
  const uint32_t playedSec = playedMs / 1000u;
  auto &d = M5Cardputer.Display;
  constexpr int kTy = 28;
  constexpr int kTW = 100;
  const int x0 = d.width() - kTW;
  d.fillRect(x0, kTy, kTW, 9, TFT_BLACK);

  char line[28];
  char elb[8];
  char tsb[8];
  formatMp3MmSs(elb, sizeof(elb), playedSec);
  if (totalSec > 0u) {
    formatMp3MmSs(tsb, sizeof(tsb), totalSec);
    snprintf(line, sizeof(line), "%s / %s", elb, tsb);
  } else {
    snprintf(line, sizeof(line), "%s / --:--", elb);
  }
  d.setTextSize(1);
  d.setTextColor(TFT_CYAN, TFT_BLACK);
  d.drawString(line, x0, kTy);
}

// One step matches MJPEG forward seek: SEEK_FRAMES (TARGET_FPS*5) @ 15 fps ≈ 5 s.
static constexpr uint32_t MP3_SEEK_STEP_MS = 1000u;
static constexpr int32_t kMp3SeekByteStep = 16000;  // ~1 s at 128 kb/s when duration unknown

// ESP8266Audio mp3->stop() calls file->close() on the source — must reopen before seek.
// filePosBeforeStop: snapshot from file->getPos() before stop; used when total duration unknown.
static bool mp3SeekByMs(AudioGeneratorMP3 *mp3, AudioFileSourceSD *file, AudioOutputI2S *out,
                         bool paused, uint32_t &playedMs, uint32_t totalSec, int32_t deltaMs,
                         const char *path, uint32_t filePosBeforeStop) {
  mp3->stop();
  out->stop();

  if (!file->open(path)) {
    return false;
  }

  const uint32_t sz = file->getSize();
  if (sz < 2u) {
    return false;
  }

  uint64_t newMs = static_cast<uint64_t>(playedMs);
  if (deltaMs < 0) {
    const uint32_t sub = static_cast<uint32_t>(-deltaMs);
    newMs = (sub >= playedMs) ? 0u : static_cast<uint64_t>(playedMs - sub);
  } else {
    newMs = static_cast<uint64_t>(playedMs) + static_cast<uint32_t>(deltaMs);
  }
  if (totalSec > 0u) {
    const uint64_t cap = static_cast<uint64_t>(totalSec) * 1000ULL;
    if (newMs > cap) {
      newMs = cap;
    }
  }
  playedMs = static_cast<uint32_t>(newMs);

  uint32_t byteOff = 0;
  if (totalSec > 0u) {
    const uint64_t totalMs = static_cast<uint64_t>(totalSec) * 1000ULL;
    byteOff = static_cast<uint32_t>((newMs * static_cast<uint64_t>(sz)) / totalMs);
    if (byteOff >= sz) {
      byteOff = sz - 1u;
    }
  } else {
    const int64_t step = (deltaMs >= 0) ? static_cast<int64_t>(kMp3SeekByteStep)
                                        : -static_cast<int64_t>(kMp3SeekByteStep);
    int64_t np = static_cast<int64_t>(filePosBeforeStop) + step;
    if (np < 0) {
      np = 0;
    } else if (np >= static_cast<int64_t>(sz)) {
      np = static_cast<int64_t>(sz) - 1;
    }
    byteOff = static_cast<uint32_t>(np);
  }

  if (!file->seek(static_cast<int32_t>(byteOff), SEEK_SET)) {
    return false;
  }
  if (!mp3->begin(file, out)) {
    return false;
  }
  if (paused) {
    out->stop();
  } else {
    applyI2sGainFromSpeakerVolume(out);
  }
  return true;
}

static void drawMp3VolumeHintTick() {
  auto &d = M5Cardputer.Display;
  const uint32_t now = millis();
  constexpr int kVolOsdW = 62;
  constexpr int kVolOsdH = 14;
  const int volX = d.width() - kVolOsdW - 2;
  if (static_cast<int32_t>(now - g_mp3VolHintUntil) >= 0) {
    if (g_mp3VolHintActive) {
      d.fillRect(volX, 1, kVolOsdW, kVolOsdH, TFT_BLACK);
      g_mp3VolHintActive = false;
    }
    return;
  }
  char buf[20];
  const int rawV = g_speakerVolumePersist;
  const int pct = (rawV * 100) / 255;
  snprintf(buf, sizeof(buf), "Vol %d%%", pct);
  const uint32_t rem = g_mp3VolHintUntil - now;
  uint16_t col = TFT_GREENYELLOW;
  if (rem < 380u) {
    col = TFT_WHITE;
  } else if (rem < 800u) {
    col = TFT_GREEN;
  } else if (rem < 1400u) {
    col = TFT_GREENYELLOW;
  }
  d.fillRect(volX, 1, kVolOsdW, kVolOsdH, TFT_BLACK);
  d.setTextColor(col, TFT_BLACK);
  d.setTextSize(1);
  d.drawString(buf, volX + 2, 4);
}

static void drawMp3LoopHintTick() {
  auto &d = M5Cardputer.Display;
  const uint32_t now = millis();
  if (static_cast<int32_t>(now - g_mp3LoopHintUntil) >= 0) {
    if (g_mp3LoopHintActive) {
      d.fillRect(3, 2, 72, 12, TFT_BLACK);
      g_mp3LoopHintActive = false;
    }
    return;
  }
  const uint32_t rem = g_mp3LoopHintUntil - now;
  uint16_t col = g_mp3LoopHintState ? TFT_GREENYELLOW : TFT_ORANGE;
  if (rem < 450u) {
    col = TFT_DARKGREY;
  } else if (rem < 900u) {
    col = g_mp3LoopHintState ? TFT_GREEN : TFT_YELLOW;
  }
  d.fillRect(3, 2, 72, 12, TFT_BLACK);
  d.setTextColor(col, TFT_BLACK);
  d.setTextSize(1);
  d.drawString(g_mp3LoopHintState ? "Loop ON" : "Loop off", 5, 4);
}

static void showLoopHintNow() {
  g_mp3LoopHintState = g_loopEnabled;
  g_mp3LoopHintUntil = millis() + 1400u;
  g_mp3LoopHintActive = true;
}

static void showSetBookmarkHintNow() {
  g_setBookmarkHintIsSet = (g_sSetMediaPath.length() > 0);
  g_setBookmarkHintUntil = millis() + 1400u;
  g_setBookmarkHintActive = true;
}

static void showKeysHintNow() {
  g_keysHintOpen = true;
  g_keysHintPainted = false;
}

static void keysHintOnHKey(bool *pBrowserNeedRedraw) {
  if (g_keysHintOpen) {
    g_keysHintOpen = false;
    g_keysHintPainted = false;
    if (pBrowserNeedRedraw) {
      *pBrowserNeedRedraw = true;
    } else {
      g_keysHintNeedFullUiRedraw = true;
    }
    s_browserHintResyncHBaselineNextPoll = true;
    return;
  }
  showKeysHintNow();
  s_browserHintResyncHBaselineNextPoll = true;
}

static void clearKeysHintForMedia() {
  g_keysHintOpen = false;
  g_keysHintPainted = false;
}

static void drawKeysHintOverlayTick(bool *pBrowserNeedRedraw) {
  auto &d = M5Cardputer.Display;
  if (!g_keysHintOpen) {
    if (g_keysHintPainted) {
      g_keysHintPainted = false;
      if (pBrowserNeedRedraw) {
        *pBrowserNeedRedraw = true;
      } else {
        g_keysHintNeedFullUiRedraw = true;
      }
    }
    return;
  }
  d.setClipRect(0, 0, d.width(), d.height());
  constexpr int margin = 3;
  const int w = d.width() - 2 * margin;
  const int h = d.height() - 2 * margin;
  d.fillRect(margin, margin, w, h, TFT_NAVY);
  d.drawRect(margin, margin, w, h, TFT_CYAN);
  d.setTextDatum(textdatum_t::top_left);
  d.setTextColor(TFT_WHITE, TFT_NAVY);
  d.setTextSize(1);
  int y = margin + 4;
  constexpr int dy = 11;
  d.drawString("Shortcuts  H toggles", margin + 4, y);
  y += dy;
  d.drawString("Browser [] ; .  S timer", margin + 4, y);
  y += dy;
  d.drawString("Enter play  Tab up  D C", margin + 4, y);
  y += dy;
  d.drawString("L A loop auto", margin + 4, y);
  y += dy;
  d.drawString("MP3: , . seek V viz", margin + 4, y);
  y += dy;
  d.drawString("- + vol  N B folder", margin + 4, y);
  y += dy;
  d.drawString("Video: P pause Tab out", margin + 4, y);
  y += dy;
  d.drawString("Hold 0 i system info", margin + 4, y);
  g_keysHintPainted = true;
}

static void drawSetBookmarkHintTick() {
  auto &d = M5Cardputer.Display;
  const uint32_t now = millis();
  constexpr int kW = 72;
  constexpr int kH = 12;
  constexpr int kY = 14;
  const int x0 = d.width() - kW - 2;
  if (static_cast<int32_t>(now - g_setBookmarkHintUntil) >= 0) {
    if (g_setBookmarkHintActive) {
      d.fillRect(x0, kY, kW, kH, TFT_BLACK);
      g_setBookmarkHintActive = false;
    }
    return;
  }
  const uint32_t rem = g_setBookmarkHintUntil - now;
  uint16_t col = g_setBookmarkHintIsSet ? TFT_GREENYELLOW : TFT_ORANGE;
  if (rem < 450u) {
    col = TFT_DARKGREY;
  } else if (rem < 900u) {
    col = g_setBookmarkHintIsSet ? TFT_GREEN : TFT_YELLOW;
  }
  d.fillRect(x0, kY, kW, kH, TFT_BLACK);
  d.setTextColor(col, TFT_BLACK);
  d.setTextSize(1);
  d.setTextDatum(textdatum_t::top_right);
  d.drawString(g_setBookmarkHintIsSet ? "Marked" : "Mark --", d.width() - 4, kY + 2);
  d.setTextDatum(textdatum_t::top_left);
}

static PlayExit playMp3File(const String &path) {
  drawMp3ScreenStatic(path);

  M5Cardputer.Speaker.setVolume(g_speakerVolumePersist);
  M5Cardputer.Speaker.stop();
  M5Cardputer.Speaker.end();
  delay(90);  // ADV: ES8311 + I2S1 release before ESP8266Audio claims the same port again

  auto *out = new AudioOutputMeterI2S(SPK_I2S_PORT);
  out->SetPinout(SPK_PIN_BCLK, SPK_PIN_LRCLK, SPK_PIN_DOUT);
  out->SetOutputModeMono(true);
#if defined(ESP32)
  out->SetBuffers(12, 2304);  // more DMA than default (5) — reduces I2S underrun crackle under display load
#endif
  applyI2sGainFromSpeakerVolume(out);
  // Do NOT call out->begin() here: AudioGeneratorMP3::begin() calls output->begin() itself. A second
  // begin() would i2s_new_channel on I2S1 again → fail with our fixed-port override → "Open/begin fail".

  const uint32_t mp3SongTotalSec = probeMp3DurationSecSd(path.c_str());

  auto *file = new AudioFileSourceSD();
  auto *mp3 = new AudioGeneratorMP3();

  uint32_t mp3PlayedAccumMs = 0;
  uint32_t mp3WallTickMs = 0;

  const auto restartMp3 = [&]() -> bool {
    mp3PlayedAccumMs = 0;
    mp3WallTickMs = 0;
    mp3->stop();
    file->close();
    if (!file->open(path.c_str())) {
      return false;
    }
    return mp3->begin(file, out);
  };

  if (!file->open(path.c_str())) {
    delete mp3;
    delete file;
    delete out;
    restoreCardputerSpeakerAfterMp3(g_speakerVolumePersist);
    M5Cardputer.Display.drawString("SD open fail", 4, 60);
    delay(800);
    markPlaybackReturnedToMenu();
    return PlayExit::MENU;
  }
  if (!mp3->begin(file, out)) {
    delete mp3;
    delete file;
    out->stop();
    delay(40);
    delete out;
    restoreCardputerSpeakerAfterMp3(g_speakerVolumePersist);
    M5Cardputer.Display.drawString("MP3/I2S start fail", 4, 60);
    delay(800);
    markPlaybackReturnedToMenu();
    return PlayExit::MENU;
  }

  resetPlaybackKeyboardBaselines();
  M5Cardputer.update();
  M5Cardputer.Keyboard.updateKeysState();
  (void)M5Cardputer.Keyboard.isChange();
  syncPlaybackKeysHintPollPrevAfterKeyboardUpdate();

  bool paused = false;
  bool overlayAudioMuted = false;
  uint32_t mp3LastPauseToggleMs = 0;
  // Start tape viz first (magnetic1 preferred by drawMp3TapeStillViz path list).
  Mp3VizMode mp3VizMode = Mp3VizMode::TAPE_STILL;
  Mp3VizMode mp3PrevVizMode = mp3VizMode;
  bool duckStaticNeedsRedraw = false;
  bool tapeStillNeedsRedraw = true;
  PlayExit outcome = PlayExit::MENU;
  bool backArmed = false;
  bool backPrevHeld = false;
  const uint32_t playbackStartMs = millis();
  for (;;) {
    M5Cardputer.update();
    applyI2sGainFromSpeakerVolume(out);
    const uint32_t mp3NowMs = millis();
    if (!paused && mp3->isRunning()) {
      if (mp3WallTickMs != 0u) {
        const uint32_t dtm = mp3NowMs - mp3WallTickMs;
        if (dtm < 4000u) {
          mp3PlayedAccumMs += dtm;
        }
      }
      mp3WallTickMs = mp3NowMs;
    } else {
      mp3WallTickMs = 0u;
    }

    M5Cardputer.Keyboard.updateKeysState();
    const bool keyChanged = M5Cardputer.Keyboard.isChange();

    if (systemInfoOverlayActive()) {
      const bool mp3HadAudio = !paused && mp3->isRunning();
      if (mp3HadAudio && !overlayAudioMuted) {
        out->stop();
        overlayAudioMuted = true;
      }
      drawSystemInfoScreen();
      delay(20);
      continue;
    }
    if (overlayAudioMuted) {
      if (!paused && mp3->isRunning()) {
        if (out->begin()) {
          applyI2sGainFromSpeakerVolume(out);
        }
      }
      overlayAudioMuted = false;
      drawMp3ScreenStatic(path);
      if (mp3VizMode == Mp3VizMode::MATRIX) {
        g_mp3MatrixLastAdvanceMs = 0;
      }
      switch (mp3VizMode) {
        case Mp3VizMode::BARS:
          drawMp3VisualizerTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::DUCK_STILL:
          drawMp3DuckVisualizerArea();
          duckStaticNeedsRedraw = false;
          break;
        case Mp3VizMode::DUCK_DANCE:
          mp3GifDanceVizTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::MATRIX:
          drawMp3MatrixRainTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::WAVE:
          drawMp3WaveTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::TAPE_STILL:
          drawMp3TapeStillViz();
          tapeStillNeedsRedraw = false;
          break;
      }
    }

    const PlayKey pk =
        mp3PollAllKeys(out, mp3VizMode, duckStaticNeedsRedraw, tapeStillNeedsRedraw, keyChanged,
                       mp3LastPauseToggleMs, backArmed, backPrevHeld, playbackStartMs);
    if (mp3VizMode != mp3PrevVizMode) {
      const bool matrixTransition =
          (mp3PrevVizMode == Mp3VizMode::MATRIX) || (mp3VizMode == Mp3VizMode::MATRIX);
      if (mp3PrevVizMode == Mp3VizMode::DUCK_DANCE) {
        mp3GifClose();
      }
      if (mp3VizMode == Mp3VizMode::DUCK_DANCE) {
        mp3GifTryOpenForDanceViz();
      }
      if (mp3VizMode == Mp3VizMode::MATRIX) {
        g_mx_R = 0;
        g_mp3MatrixLastAdvanceMs = 0;
      }
      if (matrixTransition) {
        // MATRIX uses text glyph rendering and can touch pixels outside the usual band.
        // Redraw static MP3 chrome on transitions to ensure no residue remains.
        drawMp3ScreenStatic(path);
        if (mp3VizMode == Mp3VizMode::DUCK_STILL) {
          duckStaticNeedsRedraw = true;
        }
      }
      if (mp3VizMode == Mp3VizMode::TAPE_STILL) {
        tapeStillNeedsRedraw = true;
      }
      mp3PrevVizMode = mp3VizMode;
    }
    if (pk == PlayKey::BACK_MENU) {
      outcome = PlayExit::MENU;
      break;
    }
    if (pk == PlayKey::TRACK_NEXT) {
      outcome = PlayExit::TRACK_NEXT;
      break;
    }
    if (pk == PlayKey::TRACK_PREV) {
      outcome = PlayExit::TRACK_PREV;
      break;
    }
    if (pk == PlayKey::S_SET_MEDIA) {
      g_sSetMediaPath = path;
      showSetBookmarkHintNow();
    }
    if (pk == PlayKey::SHOW_KEYS_HINT) {
      keysHintOnHKey(nullptr);
    }
    if (pk == PlayKey::PAUSE_TOGGLE) {
      paused = !paused;
      mp3LastPauseToggleMs = millis();
      // ESP32 I2S DMA otherwise repeats the last buffer → buzz when mp3->loop() stops feeding.
      if (paused) {
        out->stop();
      } else {
        if (!out->begin()) {
          paused = true;
        } else {
          applyI2sGainFromSpeakerVolume(out);
        }
      }
    }
    if (pk == PlayKey::TOGGLE_LOOP) {
      g_loopEnabled = !g_loopEnabled;
      Serial.printf("Loop %s\n", g_loopEnabled ? "ON" : "OFF");
      showLoopHintNow();
    }
    if (pk == PlayKey::TOGGLE_AUTOPLAY) {
      g_folderAutoplay = !g_folderAutoplay;
      Serial.printf("Folder autoplay %s\n", g_folderAutoplay ? "ON" : "OFF");
    }
    if (pk == PlayKey::SEEK_LEFT || pk == PlayKey::SEEK_RIGHT) {
      const int32_t d = (pk == PlayKey::SEEK_RIGHT) ? static_cast<int32_t>(MP3_SEEK_STEP_MS)
                                                    : -static_cast<int32_t>(MP3_SEEK_STEP_MS);
      mp3WallTickMs = 0u;
      const uint32_t posSnap = file->getPos();
      if (!mp3SeekByMs(mp3, file, out, paused, mp3PlayedAccumMs, mp3SongTotalSec, d, path.c_str(),
                       posSnap)) {
        if (!restartMp3()) {
          outcome = PlayExit::MENU;
          break;
        }
      }
    }

    switch (mp3VizMode) {
      case Mp3VizMode::BARS:
        drawMp3VisualizerTick(paused, &out->visEnvelope);
        break;
      case Mp3VizMode::DUCK_STILL:
        if (duckStaticNeedsRedraw) {
          drawMp3DuckVisualizerArea();
          duckStaticNeedsRedraw = false;
        }
        break;
      case Mp3VizMode::DUCK_DANCE:
        mp3GifDanceVizTick(paused, &out->visEnvelope);
        break;
      case Mp3VizMode::MATRIX:
        drawMp3MatrixRainTick(paused, &out->visEnvelope);
        break;
      case Mp3VizMode::WAVE:
        drawMp3WaveTick(paused, &out->visEnvelope);
        break;
      case Mp3VizMode::TAPE_STILL:
        if (tapeStillNeedsRedraw) {
          drawMp3TapeStillViz();
          tapeStillNeedsRedraw = false;
        }
        break;
    }
    drawMp3VolumeHintTick();
    drawMp3LoopHintTick();
    drawSetBookmarkHintTick();
    drawMp3PlaybackTimeTick(mp3PlayedAccumMs, mp3SongTotalSec);
    drawKeysHintOverlayTick(nullptr);
    if (g_keysHintNeedFullUiRedraw) {
      g_keysHintNeedFullUiRedraw = false;
      drawMp3ScreenStatic(path);
      if (mp3VizMode == Mp3VizMode::MATRIX) {
        g_mp3MatrixLastAdvanceMs = 0;
      }
      switch (mp3VizMode) {
        case Mp3VizMode::BARS:
          drawMp3VisualizerTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::DUCK_STILL:
          drawMp3DuckVisualizerArea();
          duckStaticNeedsRedraw = false;
          break;
        case Mp3VizMode::DUCK_DANCE:
          mp3GifDanceVizTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::MATRIX:
          drawMp3MatrixRainTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::WAVE:
          drawMp3WaveTick(paused, &out->visEnvelope);
          break;
        case Mp3VizMode::TAPE_STILL:
          drawMp3TapeStillViz();
          tapeStillNeedsRedraw = false;
          break;
      }
    }

    if (!paused) {
      if (mp3->isRunning()) {
        if (!mp3->loop()) {
          mp3->stop();
        }
      } else {
        if (g_loopEnabled) {
          if (!restartMp3()) {
            outcome = PlayExit::MENU;
            break;
          }
        } else {
          outcome = PlayExit::TRACK_FINISHED;
          break;
        }
      }
    } else {
      delay(12);
    }
#if defined(ESP_PLATFORM)
    delay(2);
#else
    yield();
#endif
  }

  mp3GifClose();
  mp3->stop();
  delay(30);
  // Do NOT call out->flush() on ESP32: ESP8266Audio's flush() loops while (!ConsumeSample) with delay(10)
  // and can hang forever if i2s_channel_write stops accepting data (Tab exit looks like a total freeze).
  out->stop();
  delay(120);
  delete mp3;
  file->close();
  delete file;
  delay(60);
  delete out;
  delay(150);
#if defined(ESP_PLATFORM)
  for (int i = 0; i < 16; i++) {
    yield();
    delay(10);
  }
#endif
  restoreCardputerSpeakerAfterMp3(g_speakerVolumePersist);
  markPlaybackReturnedToMenu();
  return outcome;
}

static void runBrowserMediaPlaybackLoop(const String &initialPath) {
  String cur = initialPath;
  for (;;) {
    const PlayExit ex = isMp3FileName(cur) ? playMp3File(cur) : playVideoFile(cur);
    if (ex == PlayExit::MENU) {
      break;
    }
    String nextP;
    if (ex == PlayExit::TRACK_NEXT) {
      if (!getNextMediaInFolder(cur, false, nextP)) {
        break;
      }
      cur = nextP;
      continue;
    }
    if (ex == PlayExit::TRACK_PREV) {
      if (!getPrevMediaInFolder(cur, false, nextP)) {
        break;
      }
      cur = nextP;
      continue;
    }
    if (ex == PlayExit::TRACK_FINISHED) {
      if (!g_folderAutoplay) {
        break;
      }
      if (!getNextMediaInFolder(cur, false, nextP)) {
        break;
      }
      cur = nextP;
      continue;
    }
    break;
  }
}

static void runBrowserMediaPlaybackFromFullPath(const String &path) {
  clearKeysHintForMedia();
  M5Cardputer.Display.fillScreen(TFT_BLACK);
  runBrowserMediaPlaybackLoop(path);
}

static void startBrowserPreplayCountdown(const String &path, uint32_t totalSec) {
  if (totalSec == 0u) {
    return;
  }
  g_browserPreplayPath = path;
  g_browserPreplayRemainSec = totalSec;
  g_browserPreplayNextTickMs = millis() + 1000u;
  g_browserPreplayActive = true;
  g_browserPreplayNeedSReleaseToRestart = true;
  g_browserPreplayCancelQuietStreak = 0;
  s_browserPreplayHPrev = false;
  clearKeysHintForMedia();
  // pollMenuKeys is not called while preplay runs; re-baseline S edge state on next browser poll.
  g_menuResetBrowserLetterTogglesOnNextPoll = true;
}

// After Tab cancels preplay, list highlight can disagree with the path we were counting down to; fix sel
// so TIMER_PLAY_FILE does not no-op on tp->isDir and burn the force flag.
static void browserReselectSelForPreplayPath(std::vector<MediaEntry> &entries, int &sel,
                                             const String &path) {
  if (path.length() == 0) {
    return;
  }
  const String base = displayBasename(path);
  for (size_t i = 0; i < entries.size(); ++i) {
    if (entries[i].isDir) {
      continue;
    }
    if (entries[i].fullPath == path || displayBasename(entries[i].fullPath) == base) {
      sel = static_cast<int>(i);
      return;
    }
  }
}

static void runUiLoop() {
  String cwd = "/";
  std::vector<MediaEntry> entries;
  int sel = 0;
  int scroll = 0;
  struct NavState {
    String cwd;
    int sel = 0;
    int scroll = 0;
  };
  // Stack for restoring the selection you were on when you entered a subfolder.
  // Used by Tab/Esc "UP_DIR" so it feels like a proper back button.
  std::vector<NavState> navStack;

  for (;;) {
    listMediaDir(cwd, entries);
    if (g_browserSelectPlayedMediaOnNextList && g_sSetMediaPath.length() > 0) {
      const String lastBase = displayBasename(g_sSetMediaPath);
      for (size_t i = 0; i < entries.size(); ++i) {
        if (!entries[i].isDir &&
            (entries[i].fullPath == g_sSetMediaPath ||
             displayBasename(entries[i].fullPath) == lastBase)) {
          sel = static_cast<int>(i);
          scroll = 0;
          break;
        }
      }
      g_browserSelectPlayedMediaOnNextList = false;
    }
    if (entries.empty() && cwd == "/") {
      M5Cardputer.Display.fillScreen(TFT_BLACK);
      M5Cardputer.Display.drawString("No media on SD", 4, 4);
      const uint32_t idleEnd = millis() + 500;
      for (;;) {
        M5Cardputer.update();
        M5Cardputer.Keyboard.updateKeysState();
        if (millis() >= idleEnd && !systemInfoKeysHeld()) {
          break;
        }
        if (systemInfoOverlayActive()) {
          M5Cardputer.Speaker.stop();
          drawSystemInfoScreen();
          delay(20);
          M5Cardputer.Display.fillScreen(TFT_BLACK);
          M5Cardputer.Display.drawString("No media on SD", 4, 4);
        }
        delay(25);
      }
      continue;
    }
    if (sel >= static_cast<int>(entries.size())) {
      sel = static_cast<int>(entries.size()) - 1;
    }
    if (sel < 0) {
      sel = 0;
    }

    bool needRedraw = true;
    bool browserListRegionOnlyNext = false;
    uint32_t lastNav = 0;
    uint32_t lastListMoveMs = 0;
    // >0: TCA8418 can deliver repeat-ish pressEvents / noisy edges; 0 makes the highlight "walk" every poll.
    static constexpr uint32_t kListMoveDebounceMs = 90u;
    bool menuToggleLPrev = false;
    bool menuToggleAPrev = false;
    static bool s_browserPreplayBaseDrawn = false;
    static bool s_browserPreplayWasActive = false;

    // First polls after boot/folder load can ghost `[`/`]` in keyList(); sync baselines so we don't get
    // a burst of false bracket edges (selector "walks") before any real key press.
    g_menuResetListNavEdgesOnNextPoll = true;
    while (true) {
      if (s_browserPreplayWasActive && !g_browserPreplayActive) {
        s_browserPreplayBaseDrawn = false;
        // pollMenuKeys was skipped during preplay; always resync S/D/C so timer-play works again.
        g_menuResetBrowserLetterTogglesOnNextPoll = true;
        // Tab-cancel (or any preplay→list): cursor must match g_browserPreplayPath or S targets wrong row.
        g_sSetMediaPath = g_browserPreplayPath;
        browserReselectSelForPreplayPath(entries, sel, g_browserPreplayPath);
        g_browserTimerPlayForceNextSDown = true;
      }
      s_browserPreplayWasActive = g_browserPreplayActive;
      M5Cardputer.update();
      M5Cardputer.Keyboard.updateKeysState();
      const bool keyChangedMenu = M5Cardputer.Keyboard.isChange();
      if (systemInfoOverlayActive()) {
        M5Cardputer.Speaker.stop();
        drawSystemInfoScreen();
        delay(20);
        needRedraw = true;
        delay(10);
        continue;
      }
      if (g_playDelayEditOpen) {
        tickPlayDelayEdit();
        if (!g_playDelayEditOpen) {
          needRedraw = true;
        }
        delay(10);
        continue;
      }
      if (g_browserPreplayActive) {
        // Outer loop already called update() + updateKeysState(); second poll per frame caused
        // extra churn and visible list flicker.
        const auto &stPre = M5Cardputer.Keyboard.keysState();
        const uint32_t nowTabPre = millis();
        const bool cancelHeld = browserPreplayUserCancelHeldNow(stPre);
        if (!cancelHeld) {
          if (g_browserPreplayCancelQuietStreak < 255) {
            g_browserPreplayCancelQuietStreak++;
          }
        }
        if (cancelHeld && g_browserPreplayCancelQuietStreak >= 2u) {
          g_browserPreplayActive = false;
          g_browserPreplayCancelQuietStreak = 0;
          s_browserPreplayHPrev = false;
          g_menuResetListNavEdgesOnNextPoll = true;
          g_menuResetBrowserLetterTogglesOnNextPoll = true;
          g_browserTimerPlayForceNextSDown = true;
          g_browserTimerPlayLastMs = 0u;
          g_sSetMediaPath = g_browserPreplayPath;
          browserReselectSelForPreplayPath(entries, sel, g_browserPreplayPath);
          g_menuSuppressTabEscUpDir = true;
          g_menuTabSuppressArmMs = nowTabPre;
          g_menuSyncTabEscBackBaselineOnNextPoll = true;
          needRedraw = true;
          delay(10);
          continue;
        }
        {
          const bool hPreLevel = browserPressEventsHaveDecodedHNotEnter() ||
                                 menuLetterDownWithFifo('h', 'H') ||
                                 browserHintHMatrixHeldNow();
          if (hPreLevel && !s_browserPreplayHPrev) {
            s_browserPreplayHPrev = true;
            keysHintOnHKey(&needRedraw);
          }
          if (!hPreLevel) {
            s_browserPreplayHPrev = false;
          }
        }
        // Run the 1s tick BEFORE scanning S in pressEvents. Leftover S events in the FIFO were
        // restarting the countdown on the same frame remain hit 0, so playback never started.
        const uint32_t nowPre = millis();
        bool ticked = false;
        if (static_cast<int32_t>(nowPre - g_browserPreplayNextTickMs) >= 0) {
          if (g_browserPreplayRemainSec > 0u) {
            g_browserPreplayRemainSec--;
          }
          g_browserPreplayNextTickMs = nowPre + 1000u;
          ticked = true;
          if (g_browserPreplayRemainSec == 0u) {
            g_browserPreplayActive = false;
            const String pathPlay = g_browserPreplayPath;
            if (pathPlay.length() > 0) {
              runBrowserMediaPlaybackFromFullPath(pathPlay);
            }
            listMediaDir(cwd, entries);
            needRedraw = true;
            break;
          }
        }
        if (!browserTimerPlaySHeldNow()) {
          g_browserPreplayNeedSReleaseToRestart = false;
        }
        bool sPreplayFifo = false;
        for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
          const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
          const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
          if (browserMatrixCellIsTimerPlayS(p) || browserMenuKeyMeansS(kch, kv)) {
            sPreplayFifo = true;
            break;
          }
        }
        if (sPreplayFifo && g_browserPreplayRemainSec > 0u && !g_browserPreplayNeedSReleaseToRestart) {
          g_sSetMediaPath = g_browserPreplayPath;
          const uint32_t sec =
              (g_playStartDelaySec > 0u) ? g_playStartDelaySec : kTimerPlayDefaultDelaySec;
          startBrowserPreplayCountdown(g_browserPreplayPath, sec);
          needRedraw = true;
          delay(10);
          continue;
        }
        // Avoid fillScreen every poll (was ~100 Hz) — that caused visible flicker. Paint the list once,
        // then only refresh the banner + HUD when the second ticks or something forces a full redraw.
        if (!s_browserPreplayBaseDrawn || needRedraw) {
          drawBrowser(cwd, entries, sel, scroll, false);
          s_browserPreplayBaseDrawn = true;
          needRedraw = false;
        } else if (ticked) {
          drawBrowserPreplayCountdownBanner();
          drawBrowserTopRightOverlays();
        }
        drawKeysHintOverlayTick(&needRedraw);
        delay(10);
        continue;
      }
      if (needRedraw) {
        drawBrowser(cwd, entries, sel, scroll, browserListRegionOnlyNext);
        if (g_debugShowTabExit) {
          // Debug marker disabled for runtime reliability (avoid post-Tab input stalls).
          g_debugShowTabExit = false;
        }
        browserListRegionOnlyNext = false;
        needRedraw = false;
      }
      drawKeysHintOverlayTick(&needRedraw);

      const MenuAction a = pollMenuKeys(keyChangedMenu, menuToggleLPrev, menuToggleAPrev);
      if (a == MenuAction::SHOW_KEYS_HINT) {
        keysHintOnHKey(nullptr);
        drawBrowser(cwd, entries, sel, scroll, false);
        browserListRegionOnlyNext = false;
        needRedraw = false;
        drawKeysHintOverlayTick(nullptr);
        lastNav = millis();
        delay(10);
        continue;
      }
      if (a == MenuAction::TOGGLE_LOOP) {
        g_loopEnabled = !g_loopEnabled;
        needRedraw = true;
        lastNav = millis();
        delay(10);
        continue;
      }
      if (a == MenuAction::TOGGLE_AUTOPLAY) {
        g_folderAutoplay = !g_folderAutoplay;
        needRedraw = true;
        lastNav = millis();
        delay(10);
        continue;
      }
      if (a == MenuAction::OPEN_DELAY_EDITOR) {
        openPlayDelayEdit();
        lastNav = millis();
        delay(10);
        continue;
      }
      if (a == MenuAction::TOGGLE_COUNTDOWN_HUD) {
        g_playStartCountdownHudVisible = !g_playStartCountdownHudVisible;
        needRedraw = true;
        lastNav = millis();
        delay(10);
        continue;
      }
      if (a == MenuAction::UP_DIR) {
        if (!navStack.empty()) {
          const NavState prev = navStack.back();
          navStack.pop_back();
          cwd = prev.cwd;
          listMediaDir(cwd, entries);
          sel = prev.sel;
          scroll = prev.scroll;
          needRedraw = true;
        } else if (cwd != "/") {
          // Fallback if stack wasn't built (shouldn't normally happen).
          cwd = pathParent(cwd);
          listMediaDir(cwd, entries);
          sel = 0;
          scroll = 0;
          needRedraw = true;
        }
        lastNav = millis();
        delay(1);    // minimal settle time for keyboard/selection state
        continue;
      }
      if (a == MenuAction::ENTER) {
        if (entries.empty()) {
          lastNav = millis();
          delay(10);
          continue;
        }
        const MediaEntry &pick = entries[static_cast<size_t>(sel)];
        if (pick.isDir) {
          navStack.push_back(NavState{cwd, sel, scroll});
          cwd = pick.fullPath;
          listMediaDir(cwd, entries);
          sel = 0;
          scroll = 0;
          needRedraw = true;
          delay(10);
          continue;
        }
        // Enter: play immediately. Pre-play countdown is S-only (see TIMER_PLAY_FILE).
        runBrowserMediaPlaybackFromFullPath(pick.fullPath);
        listMediaDir(cwd, entries);
        needRedraw = true;
        break;
      }
      if (a == MenuAction::TIMER_PLAY_FILE) {
        if (entries.empty()) {
          g_browserTimerPlayForceNextSDown = true;
          lastNav = millis();
          delay(10);
          continue;
        }
        if (sel < 0 || static_cast<size_t>(sel) >= entries.size()) {
          browserReselectSelForPreplayPath(entries, sel, g_browserPreplayPath);
        }
        if (sel < 0 || static_cast<size_t>(sel) >= entries.size()) {
          g_browserTimerPlayForceNextSDown = true;
          lastNav = millis();
          delay(10);
          continue;
        }
        const size_t selIdx = static_cast<size_t>(sel);
        const MediaEntry *tp = &entries[selIdx];
        // If selection ended up on a directory after returning from playback,
        // fall back to the last-played media (bookmark path) so S still works.
        if (tp->isDir && g_sSetMediaPath.length() > 0) {
          const String lastBase = displayBasename(g_sSetMediaPath);
          for (const MediaEntry &e : entries) {
            if (!e.isDir &&
                (e.fullPath == g_sSetMediaPath ||
                 displayBasename(e.fullPath) == lastBase)) {
              tp = &e;
              break;
            }
          }
        }
        if (tp->isDir && g_browserPreplayPath.length() > 0) {
          browserReselectSelForPreplayPath(entries, sel, g_browserPreplayPath);
          if (sel >= 0 && static_cast<size_t>(sel) < entries.size()) {
            tp = &entries[static_cast<size_t>(sel)];
          }
        }
        if (tp->isDir) {
          g_browserTimerPlayForceNextSDown = true;
          lastNav = millis();
          delay(10);
          continue;
        }
        // S: bind bookmark to the highlighted file, full-screen countdown, then play. Seconds = D editor
        // (play-start delay) when > 0; if D is 0, use kTimerPlayDefaultDelaySec so S always counts down.
        g_sSetMediaPath = tp->fullPath;
        const uint32_t sec =
            (g_playStartDelaySec > 0u) ? g_playStartDelaySec : kTimerPlayDefaultDelaySec;
        startBrowserPreplayCountdown(tp->fullPath, sec);
        needRedraw = true;
        delay(10);
        continue;
      }
      if (a == MenuAction::UP) {
        if (sel > 0 && (millis() - lastListMoveMs) >= kListMoveDebounceMs) {
          sel--;
          needRedraw = true;
          browserListRegionOnlyNext = true;
          lastListMoveMs = millis();
        }
        lastNav = millis();
      } else if (a == MenuAction::DOWN) {
        if (sel + 1 < static_cast<int>(entries.size()) &&
            (millis() - lastListMoveMs) >= kListMoveDebounceMs) {
          sel++;
          needRedraw = true;
          browserListRegionOnlyNext = true;
          lastListMoveMs = millis();
        }
        lastNav = millis();
      }

      // Hold-repeat removed: one move per press in browser list.

      delay(8);
    }
  }
}

void setup() {
  Serial.begin(115200);
  M5Cardputer.begin();
  M5Cardputer.Display.setRotation(1);
  M5Cardputer.Display.setBrightness(200);

  if (!initSd()) {
    drawStartupSplashFrame(false);
    delay(1600);
    M5Cardputer.Display.drawString("SD fail", 4, 4);
    return;
  }

  drawStartupSplashFrame(true);

  g_mjpegBuf = (uint8_t *)malloc(MJPEG_BUFFER_SIZE);
  g_audioBuf = (uint8_t *)malloc(AUDIO_CHUNK);
  if (!g_mjpegBuf || !g_audioBuf) {
    Serial.println("malloc buffer failed");
    delay(1600);
    return;
  }

  M5Cardputer.Speaker.begin();
  setSpeakerVolumePersisted(kStartupVolumePct * 255 / 100);
  playSplashJingleFromSdIfPresent();

#if defined(ESP_PLATFORM)
  randomSeed(static_cast<uint32_t>(esp_random()));
#endif

  runUiLoop();
}

void loop() {
  delay(1000);
}
