/*
 * cardputerBasicAV — for M5Stack Cardputer ADV (ESP32-S3 + ES8311 codec path via M5Unified).
 * (Developed on ADV; base Cardputer may work but pins/audio/I2C codec behavior are not verified here.)
 *
 * MJPEG (+ optional .pcm), MP3, file menu, seek, loop. SD root: .mjpeg / .mjpg (+ optional .pcm) and/or .mp3
 *
 * Browser: Enter = open/play; Tab/Esc = up; [ ] nav; L=file loop; A=folder autoplay (next at end; no wrap past last file).
 * Video: P or BtnA pause; Tab/Esc = menu; , / or arrows seek; L/A as above; - = vol.
 * MP3: V cycles viz (bars / ducks / matrix: ASCII streams traverse MP3 band top→bottom; rot 1 → fall along logical X); , / or arrows seek (~1s); N/B = next/prev track in folder (stops at folder ends). Top-right time = elapsed/total when ID3 TLEN or Xing/Info present.
 * Hold 0 or i ~0.05s: system info (battery, etc.); release to resume. Audio is muted for that screen so the long draw cannot I2S-underrun (buzz). Overlay draws once; light poll while held.
 * Startup splash uses splash_duck_rgb565.h; optional root SD clip /startTape.mp3 during splash (see kSplashJinglePath).
 * Matching PNG placeholder: assets/splash_duck_placeholder.png
 *
 * MP3 needs: ESP8266Audio. AnimatedGIF (bitbank2) is bundled as AnimatedGIF.cpp / .h / gif.inl next to this sketch.
 * MP3 I2S: AudioOutputMeterI2S::begin() overrides ESP8266Audio to use I2S_NUM_1 (SPK_I2S_PORT) instead of
 * I2S_NUM_AUTO, and avoids assert() on alloc failure — fixes Tab→next MP3 reboot on Cardputer ADV.
 *
 * Convert video: scripts/mp4_to_car    puter_mjpeg.sh
 *$ ffmpeg -y -i Your.mp4   -vf "scale=240:135:force_original_aspect_ratio=increase,crop=240:135"   -r 15 -q:v 8 -an Your.mjpeg
 *$ ffmpeg -y -i Your.mp4   -map 0:a:0 -f u8 -acodec pcm_u8 -ar 44100 -ac 1 Your.pcm
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
#include "AnimatedGIF.h"
#include <math.h>

// Types must come before any static functions: Arduino inserts function prototypes right after #includes,
// so listMediaDir / pollMenuKeys / playMp3File prototypes would otherwise see these names undefined.
enum class MenuAction { NONE, ENTER, UP, DOWN, TOGGLE_LOOP, UP_DIR, TOGGLE_AUTOPLAY };

enum class PlayExit { MENU, TRACK_FINISHED, TRACK_NEXT, TRACK_PREV };

struct MediaEntry {
  String label;
  String fullPath;
  bool isDir;
};

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
};

enum class Mp3VizMode : uint8_t { BARS = 0, DUCK_STILL, DUCK_DANCE, MATRIX, WAVE };

static constexpr uint8_t MP3_VIZ_MODE_COUNT = 5;

static constexpr int TARGET_FPS = 15;
static constexpr uint32_t FRAME_MS = 1000 / TARGET_FPS;
static constexpr unsigned AUDIO_RATE = 44100;
static constexpr size_t AUDIO_CHUNK = AUDIO_RATE / static_cast<unsigned>(TARGET_FPS);
static constexpr int SEEK_FRAMES = TARGET_FPS;

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

static uint32_t g_mp3VolHintUntil = 0;
static bool g_mp3VolHintActive = false;
static uint32_t g_mp3LoopHintUntil = 0;
static bool g_mp3LoopHintActive = false;
static bool g_mp3LoopHintState = false;

// Volume UI can cause short keyboard ghosting on ADV; if we see a "p" toggle during
// that window, ignore it to prevent accidental pause when changing volume.
static uint32_t g_ignorePauseToggleUntilMs = 0;

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

// After Tab/Esc exits MP3/video, the key can still be down; ignore UP_DIR from Tab/Esc until released (avoids WDT/spurious nav).
static bool g_menuSuppressTabEscUpDir = false;
// After exiting playback, Enter can remain electrically "stuck" for a frame and re-open media immediately.
// Ignore Enter until it is fully released once.
static bool g_menuSuppressEnterUntilRelease = false;
static uint32_t g_menuSuppressEnterUntilMs = 0;
static constexpr uint32_t kMenuEnterReleaseGuardMs = 350u;
static uint32_t g_menuLastEnterAtMs = 0;
static constexpr uint32_t kMenuEnterMinGapMs = 120u;
static bool g_trackNavAwaitRelease = false;
static bool g_trackNavPrevN = false;
static bool g_trackNavPrevB = false;
// Video loop side-channel: +1 next, -1 prev, 0 none.
static int g_videoTrackNavRequest = 0;

static void markPlaybackReturnedToMenu() {
  g_menuSuppressTabEscUpDir = true;
  g_menuSuppressEnterUntilRelease = true;
  g_menuSuppressEnterUntilMs = millis() + kMenuEnterReleaseGuardMs;
}

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

// Unified N/B track navigation detector (shared by MP3 + video paths).
// Guarantees one physical press => one track step, requiring release before next step.
static PlayKey pollTrackNavNextPrev() {
  static uint32_t trackNavLatchedAtMs = 0;
  static constexpr uint32_t kTrackNavLatchMaxMs = 900u;
  bool nHeld = M5Cardputer.Keyboard.isKeyPressed('n') || M5Cardputer.Keyboard.isKeyPressed('N');
  bool bHeld = M5Cardputer.Keyboard.isKeyPressed('b') || M5Cardputer.Keyboard.isKeyPressed('B');

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

  // Fallback edges when pressEvents miss an event under load.
  if (nHeld && !g_trackNavPrevN) {
    nEdge = true;
    if (lastDir == 0) {
      lastDir = +1;
    }
  }
  if (bHeld && !g_trackNavPrevB) {
    bEdge = true;
    if (lastDir == 0) {
      lastDir = -1;
    }
  }
  g_trackNavPrevN = nHeld;
  g_trackNavPrevB = bHeld;

  const uint32_t now = millis();
  if (!nHeld && !bHeld) {
    g_trackNavAwaitRelease = false;
  } else if (g_trackNavAwaitRelease && (now - trackNavLatchedAtMs) > kTrackNavLatchMaxMs) {
    // Safety unlock for cases where video polling misses release transitions.
    g_trackNavAwaitRelease = false;
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

static void drawStartupSplashFrame() {
  auto &d = M5Cardputer.Display;
  d.fillScreen(0x4D7B);
  const int dw = d.width();
  const int dh = d.height();
  const int ix = (dw - SPLASH_DUCK_W) / 2;
  const int iy = (dh - SPLASH_DUCK_H) / 2 - 14;
  d.pushImage(ix, iy, SPLASH_DUCK_W, SPLASH_DUCK_H, SPLASH_DUCK_RGB565);
  d.setTextSize(1);
  d.setTextColor(TFT_WHITE, 0x4D7B);
  d.drawCenterString("cardputerBasicAV", dw / 2, dh - 32);
  d.setTextColor(TFT_CYAN, 0x4D7B);
  d.drawCenterString("Cardputer ADV", dw / 2, dh - 20);
  d.setTextColor(TFT_WHITE, 0x4D7B);
  d.drawCenterString("MJPEG / MP3", dw / 2, dh - 8);
}

// Last unambiguous volume direction seen from pressEvents().
// -1 = down, +1 = up, 0 = unknown.
static int g_volLastDir = 0;
static bool g_volDownHeldPrev = false;
static bool g_volUpHeldPrev = false;

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
    if (volMatrixCellIsDown(p)) {
      matrixDownNow = true;
    }
    if (volMatrixCellIsUp(p)) {
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
    if (byteMeansVolDown(kch)) {
      evDir = -1;
    }
    if (byteMeansVolUp(kch)) {
      evDir = +1;
    }
    if (evDir == 0) {
      const KeyValue_t kv = M5Cardputer.Keyboard.getKeyValue(p);
      if (keyValueMeansVolDown(kv)) {
        evDir = -1;
      } else if (keyValueMeansVolUp(kv)) {
        evDir = +1;
      }
    }
    if (evDir == 0) {
      if (volMatrixCellIsDown(p)) {
        evDir = -1;
      } else if (volMatrixCellIsUp(p)) {
        evDir = +1;
      }
    }
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
                             bool &pcmOpen, int nextFrameIdx) {
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

  for (int i = 0; i < nextFrameIdx; i++) {
    if (!skipOneJpegFrame(v)) {
      return false;
    }
  }

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

static void drawBrowser(const String &cwd, const std::vector<MediaEntry> &entries, int sel, int &scroll) {
  auto &d = M5Cardputer.Display;
  d.fillScreen(TFT_BLACK);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  d.setTextSize(1);
  {
    String head = cwd.length() > 22 ? String("..") + cwd.substring(cwd.length() - 20) : cwd;
    d.drawString(String("Dir: ") + head, 2, 2);
  }
  d.setTextColor(g_loopEnabled ? TFT_GREENYELLOW : TFT_DARKGREY, TFT_BLACK);
  d.drawString(g_loopEnabled ? "Loop: ON (L)" : "Loop: off (L)", 2, 12);
  d.setTextColor(g_folderAutoplay ? TFT_GREENYELLOW : TFT_DARKGREY, TFT_BLACK);
  d.drawString(g_folderAutoplay ? "Auto: ON (A)" : "Auto: off (A)", 2, 22);
  d.setTextColor(TFT_WHITE, TFT_BLACK);
  if (entries.empty()) {
    d.drawString("Empty folder", 2, 32);
    d.setTextColor(TFT_CYAN, TFT_BLACK);
    d.drawString("Tab/Esc=up  [ ]  L/A  0/i=info", 2, d.height() - 10);
    return;
  }
  if (sel < scroll) {
    scroll = sel;
  }
  if (sel >= scroll + MENU_LINES) {
    scroll = sel - MENU_LINES + 1;
  }
  int y = 34;
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
  d.setTextColor(TFT_CYAN, TFT_BLACK);
  d.drawString("Ent=open  Tab/Esc  [ ]  L/A  0/i=info", 2, d.height() - 10);
}

// Caller runs M5Cardputer.update(), keyChanged = isChange(), updateKeysState().
// Edge-detect L/A so keyboard repeat does not spin (continues that skip delay(10) → WDT reset).
static MenuAction pollMenuKeys(bool keyChanged, bool &toggleLPrev, bool &toggleAPrev) {
  (void)keyChanged;
  const auto &st = M5Cardputer.Keyboard.keysState();
  static bool navUpPrev = false;
  static bool navDownPrev = false;
  static bool enterPrevHeld = false;
  static uint32_t navLastMoveAtMs = 0;
  static constexpr uint32_t kMenuNavMinGapMs = 85u;

  if (g_menuSuppressTabEscUpDir) {
    if (!tabEscHeldNow(st)) {
      g_menuSuppressTabEscUpDir = false;
    }
  }
  if (g_menuSuppressEnterUntilRelease) {
    const bool enterNow = enterHeldNow(st);
    const bool timeoutElapsed = static_cast<int32_t>(millis() - g_menuSuppressEnterUntilMs) >= 0;
    if (!enterNow || timeoutElapsed) {
      g_menuSuppressEnterUntilRelease = false;
    }
  }

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

  if (!g_menuSuppressTabEscUpDir) {
    if (tabEscBackRequested(st)) {
      return MenuAction::UP_DIR;
    }
  }

  // Enter in browser:
  // - accept physical press-edge when available
  // - fall back to held-state rising-edge if pressEvents are throttled
  // - rate-limit slightly to avoid accidental double-open
  const bool enterHeld = enterHeldNow(st);
  const bool enterEdge = enterPressedEdgeNow();
  const bool enterRising = enterHeld && !enterPrevHeld;
  enterPrevHeld = enterHeld;
  if (!g_menuSuppressEnterUntilRelease && (enterEdge || enterRising)) {
    const uint32_t now = millis();
    if ((now - g_menuLastEnterAtMs) >= kMenuEnterMinGapMs) {
      g_menuLastEnterAtMs = now;
      return MenuAction::ENTER;
    }
  }

  // Fast one-step list navigation from held-state rising edges:
  // '[' or ';' (and ':') => UP, ']' or '.' => DOWN.
  bool navUpEdge = false;
  bool navDownEdge = false;
  int navLastDir = 0;  // -1 up, +1 down
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    int evDir = 0;
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    if (kch == static_cast<uint8_t>('[') || kch == static_cast<uint8_t>(';') ||
        kch == static_cast<uint8_t>(':')) {
      evDir = -1;
    } else if (kch == static_cast<uint8_t>(']') || kch == static_cast<uint8_t>('.')) {
      evDir = +1;
    }
    if (evDir == 0) {
      if ((p.x == 11 && p.y == 1) || (p.x == 11 && p.y == 2)) {
        evDir = -1;
      } else if ((p.x == 12 && p.y == 1) || (p.x == 11 && p.y == 3)) {
        evDir = +1;
      }
    }
    if (evDir < 0) {
      navUpEdge = true;
      navLastDir = -1;
    } else if (evDir > 0) {
      navDownEdge = true;
      navLastDir = +1;
    }
  }
  const uint32_t navNowMs = millis();
  if ((navNowMs - navLastMoveAtMs) >= kMenuNavMinGapMs) {
    if (navUpEdge && !navDownEdge) {
      navLastMoveAtMs = navNowMs;
      return MenuAction::UP;
    }
    if (!navUpEdge && navDownEdge) {
      navLastMoveAtMs = navNowMs;
      return MenuAction::DOWN;
    }
    if (navUpEdge && navDownEdge) {
      navLastMoveAtMs = navNowMs;
      return (navLastDir < 0) ? MenuAction::UP : MenuAction::DOWN;
    }
  }

  bool navUpNow = M5Cardputer.Keyboard.isKeyPressed('[') ||
                  M5Cardputer.Keyboard.isKeyPressed(';') ||
                  M5Cardputer.Keyboard.isKeyPressed(':');
  bool navDownNow = M5Cardputer.Keyboard.isKeyPressed(']') ||
                    M5Cardputer.Keyboard.isKeyPressed('.');
  for (const Point2D_t &p : M5Cardputer.Keyboard.keyList()) {
    if ((p.x == 11 && p.y == 1) || (p.x == 11 && p.y == 2)) {  // '[' or ';' / ':'
      navUpNow = true;
    } else if ((p.x == 12 && p.y == 1) || (p.x == 11 && p.y == 3)) {  // ']' or '.'
      navDownNow = true;
    }
  }
  if (navUpNow && !navUpPrev) {
    if ((navNowMs - navLastMoveAtMs) < kMenuNavMinGapMs) {
      navUpPrev = navUpNow;
      navDownPrev = navDownNow;
      return MenuAction::NONE;
    }
    navLastMoveAtMs = navNowMs;
    navUpPrev = navUpNow;
    navDownPrev = navDownNow;
    return MenuAction::UP;
  }
  if (navDownNow && !navDownPrev) {
    if ((navNowMs - navLastMoveAtMs) < kMenuNavMinGapMs) {
      navUpPrev = navUpNow;
      navDownPrev = navDownNow;
      return MenuAction::NONE;
    }
    navLastMoveAtMs = navNowMs;
    navUpPrev = navUpNow;
    navDownPrev = navDownNow;
    return MenuAction::DOWN;
  }
  navUpPrev = navUpNow;
  navDownPrev = navDownNow;

  return MenuAction::NONE;
}

// Caller runs M5Cardputer.update(), then keyChanged = Keyboard.isChange(), then updateKeysState().
static PlayKey pollPlaybackKeys(bool keyChanged, bool &backArmed, bool &backPrevHeld,
                                uint32_t playbackStartMs) {
  (void)keyChanged;
  pollVolumeKeysMatrix(nullptr);

  if (M5Cardputer.BtnA.wasClicked()) {
    return PlayKey::PAUSE_TOGGLE;
  }

  const auto &st = M5Cardputer.Keyboard.keysState();

  if (playbackBackEdge(st, backArmed, backPrevHeld, playbackStartMs)) {
    return PlayKey::BACK_MENU;
  }
  const PlayKey nb = pollTrackNavNextPrev();
  if (nb == PlayKey::TRACK_NEXT || nb == PlayKey::TRACK_PREV) {
    return nb;
  }
  if (!keyChanged) {
    return PlayKey::NONE;
  }
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

  for (char c : st.word) {
    if (c == ',') {
      return PlayKey::SEEK_LEFT;
    }
    if (c == '/') {
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

static bool applySeekBack(const String &videoPath, const String &pcmPath, File &v, File &pcm,
                          bool &pcmOpen, int &nextFrameIdx) {
  nextFrameIdx -= SEEK_FRAMES;
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
    const bool keyChanged = M5Cardputer.Keyboard.isChange();
    M5Cardputer.Keyboard.updateKeysState();
    if (systemInfoOverlayActive()) {
      if (pcmOpen) {
        M5Cardputer.Speaker.stop();
      }
      drawSystemInfoScreen();
      delay(20);
      frameStartMs = millis();
      continue;
    }

    const PlayKey pk = pollPlaybackKeys(keyChanged, backArmed, backPrevHeld, playbackStartMs);
    drawMp3LoopHintTick();
    drawMp3VolumeHintTick();

    if (pk == PlayKey::BACK_MENU) {
      return false;
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
      frameStartMs = millis();
      continue;
    }
    if (pk == PlayKey::SEEK_LEFT) {
      if (!applySeekBack(videoPath, pcmPath, v, pcm, pcmOpen, nextFrameIdx)) {
        return false;
      }
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
      const bool keyChanged = M5Cardputer.Keyboard.isChange();
      M5Cardputer.Keyboard.updateKeysState();
      if (systemInfoOverlayActive()) {
        if (pcmOpen) {
          M5Cardputer.Speaker.stop();
        }
        drawSystemInfoScreen();
        delay(20);
        continue;
      }
      const PlayKey pk = pollPlaybackKeys(keyChanged, backArmed, backPrevHeld, playbackStartMs);
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
      } else if (pk == PlayKey::SEEK_LEFT) {
        applySeekBack(videoPath, pcmPath, v, pcmFile, pcmOpen, nextFrameIdx);
      } else if (pk == PlayKey::TRACK_NEXT) {
        outcome = PlayExit::TRACK_NEXT;
        break;
      } else if (pk == PlayKey::TRACK_PREV) {
        outcome = PlayExit::TRACK_PREV;
        break;
      }
      drawMp3LoopHintTick();
      drawMp3VolumeHintTick();
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
    drawMp3VolumeHintTick();
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
                              bool keyChanged, uint32_t &lastPauseToggleMs, bool &backArmed,
                              bool &backPrevHeld, uint32_t playbackStartMs) {
  const auto &st = M5Cardputer.Keyboard.keysState();
  if (playbackBackEdge(st, backArmed, backPrevHeld, playbackStartMs)) {
    return PlayKey::BACK_MENU;
  }

  if (M5Cardputer.BtnA.wasClicked()) {
    return PlayKey::PAUSE_TOGGLE;
  }

  pollVolumeKeysMatrix(out);

  const PlayKey nb = pollTrackNavNextPrev();
  if (nb == PlayKey::TRACK_NEXT || nb == PlayKey::TRACK_PREV) {
    return nb;
  }

  const uint32_t now = millis();
  if (keyChanged) {
    for (char c : st.word) {
      if (c == 'p' || c == 'P') {
        if (static_cast<int32_t>(now - g_ignorePauseToggleUntilMs) < 0) {
          // Ignore accidental pause toggles shortly after volume input.
          break;
        }
        // Debounce here only; playMp3File stamps lastPauseToggleMs on any pause (incl. BtnA).
        if (now - lastPauseToggleMs >= kMp3PauseToggleDebounceMs) {
          return PlayKey::PAUSE_TOGGLE;
        }
        break;
      }
    }
  }

  // `V` / `v`: cycle visual mode (edge-based for responsiveness on ADV).
  for (const Point2D_t &p : M5Cardputer.Keyboard.pressEvents()) {
    const uint8_t kch = M5Cardputer.Keyboard.getKey(p);
    if (kch == static_cast<uint8_t>('v') || kch == static_cast<uint8_t>('V')) {
      vizMode = static_cast<Mp3VizMode>((static_cast<uint8_t>(vizMode) + 1u) % MP3_VIZ_MODE_COUNT);
      if (vizMode == Mp3VizMode::DUCK_STILL) {
        duckStaticNeedsRedraw = true;
      }
      return PlayKey::NONE;
    }
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

  for (char c : st.word) {
    if (c == 'v' || c == 'V') {
      vizMode = static_cast<Mp3VizMode>((static_cast<uint8_t>(vizMode) + 1u) % MP3_VIZ_MODE_COUNT);
      if (vizMode == Mp3VizMode::DUCK_STILL) {
        duckStaticNeedsRedraw = true;
      }
      return PlayKey::NONE;
    }
  }
  return PlayKey::NONE;
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

// One step matches MJPEG seek: SEEK_FRAMES (15) @ 15 fps ≈ 1 s.
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
    return PlayExit::MENU;
  }

  bool paused = false;
  bool overlayAudioMuted = false;
  uint32_t mp3LastPauseToggleMs = 0;
  Mp3VizMode mp3VizMode = Mp3VizMode::BARS;
  Mp3VizMode mp3PrevVizMode = mp3VizMode;
  bool duckStaticNeedsRedraw = false;
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

    const bool keyChanged = M5Cardputer.Keyboard.isChange();
    M5Cardputer.Keyboard.updateKeysState();

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
      }
    }

    const PlayKey pk = mp3PollAllKeys(out, mp3VizMode, duckStaticNeedsRedraw, keyChanged,
                                      mp3LastPauseToggleMs, backArmed, backPrevHeld,
                                      playbackStartMs);
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
    }
    drawMp3VolumeHintTick();
    drawMp3LoopHintTick();
    drawMp3PlaybackTimeTick(mp3PlayedAccumMs, mp3SongTotalSec);

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

static void runUiLoop() {
  String cwd = "/";
  std::vector<MediaEntry> entries;
  int sel = 0;
  int scroll = 0;

  for (;;) {
    listMediaDir(cwd, entries);
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
    uint32_t lastNav = 0;
    uint32_t lastListMoveMs = 0;
    static constexpr uint32_t kListMoveDebounceMs = 0u;
    bool menuToggleLPrev = false;
    bool menuToggleAPrev = false;

    while (true) {
      M5Cardputer.update();
      const bool keyChanged = M5Cardputer.Keyboard.isChange();
      M5Cardputer.Keyboard.updateKeysState();
      if (systemInfoOverlayActive()) {
        M5Cardputer.Speaker.stop();
        drawSystemInfoScreen();
        delay(20);
        needRedraw = true;
        delay(10);
        continue;
      }
      if (needRedraw) {
        drawBrowser(cwd, entries, sel, scroll);
        needRedraw = false;
      }

      const MenuAction a = pollMenuKeys(keyChanged, menuToggleLPrev, menuToggleAPrev);
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
      if (a == MenuAction::UP_DIR) {
        if (cwd != "/") {
          cwd = pathParent(cwd);
          listMediaDir(cwd, entries);
          sel = 0;
          scroll = 0;
          needRedraw = true;
        }
        lastNav = millis();
        delay(10);
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
          cwd = pick.fullPath;
          listMediaDir(cwd, entries);
          sel = 0;
          scroll = 0;
          needRedraw = true;
          delay(10);
          continue;
        }
        M5Cardputer.Display.fillScreen(TFT_BLACK);
        String cur = pick.fullPath;
        for (;;) {
          const PlayExit ex =
              isMp3FileName(cur) ? playMp3File(cur) : playVideoFile(cur);
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
        listMediaDir(cwd, entries);
        needRedraw = true;
        break;
      }
      if (a == MenuAction::UP) {
        if (sel > 0 && (millis() - lastListMoveMs) >= kListMoveDebounceMs) {
          sel--;
          needRedraw = true;
          lastListMoveMs = millis();
        }
        lastNav = millis();
      } else if (a == MenuAction::DOWN) {
        if (sel + 1 < static_cast<int>(entries.size()) &&
            (millis() - lastListMoveMs) >= kListMoveDebounceMs) {
          sel++;
          needRedraw = true;
          lastListMoveMs = millis();
        }
        lastNav = millis();
      }

      // Hold-repeat removed: one move per press in browser list.

      delay(1);
    }
  }
}

void setup() {
  Serial.begin(115200);
  M5Cardputer.begin();
  M5Cardputer.Display.setRotation(1);
  M5Cardputer.Display.setBrightness(200);
  drawStartupSplashFrame();

  g_mjpegBuf = (uint8_t *)malloc(MJPEG_BUFFER_SIZE);
  g_audioBuf = (uint8_t *)malloc(AUDIO_CHUNK);
  if (!g_mjpegBuf || !g_audioBuf) {
    Serial.println("malloc buffer failed");
    delay(1600);
    return;
  }

  if (!initSd()) {
    delay(1600);
    M5Cardputer.Display.drawString("SD fail", 4, 4);
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
