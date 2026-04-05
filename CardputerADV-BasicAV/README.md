# CardputerADV-BasicAV (v1.0)

Audio and video playback for the **M5Stack Cardputer ADV** (MJPEG + optional PCM, MP3, file browser, seek, loop).

Put media on an SD card and open this sketch in the Arduino IDE (or your usual ESP32 toolchain).

## Source layout

- **Sketch:** `CardputerADV-BasicAV/CardputerADV-BasicAV.ino` (folder name matches the `.ino` for Arduino).

## Dependencies

- **M5Unified** (and Cardputer board support as usual for the ADV).
- **ESP8266Audio** for MP3.

See the comment block at the top of `CardputerADV-BasicAV.ino` for ffmpeg examples and hardware notes.

## Minimal media (optional)

Sample assets are useful for a first run (splash, jingle, GIF visual, sample clip). Paths the sketch may use:

- `assets/tape-o-magnetic.png` and `assets/tape-o-magnetic1.png` (startup splash)
- `assets/startTape.mp3` (startup jingle)
- `assets/dancing-duck-colorful-happy-duck.gif` (MP3 “duck dance” visual)
- `assets/video.mjpeg` (sample video)

## SD card layout

Copy an `assets/` folder to the **root** of the SD card so files appear as `/assets/...` (or add your own media at the paths you prefer; the sketch documents defaults in the header comment).
