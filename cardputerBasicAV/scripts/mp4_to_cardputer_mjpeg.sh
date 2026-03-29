#!/usr/bin/env bash
# Convert MP4 to MJPEG + optional PCM for cardputerBasicAV / Cardputer ADV (same basename: video.mjpeg + video.pcm).
# Copy both files to the SD card root (FAT32).
#
# Usage:
#   ./scripts/mp4_to_cardputer_mjpeg.sh /path/to/clip.mp4
#   ./scripts/mp4_to_cardputer_mjpeg.sh clip.mp4 /media/USER/SDCARD
#
# First 60 seconds only (put duration BEFORE -i so audio length matches):
#   DURATION=60 ./scripts/mp4_to_cardputer_mjpeg.sh clip.mp4
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
die() { echo "error: $*" >&2; exit 1; }

[[ "${1:-}" ]] || die "usage: $0 <input.mp4> [output_directory]"

IN="$1"
[[ -f "$IN" ]] || die "not a file: $IN"

OUT_DIR="${2:-.}"
mkdir -p "$OUT_DIR"
OUT_V="${OUT_DIR}/video.mjpeg"
OUT_A="${OUT_DIR}/video.pcm"

command -v ffmpeg >/dev/null 2>&1 || die "install ffmpeg (e.g. sudo apt install ffmpeg)"
command -v ffprobe >/dev/null 2>&1 || die "install ffprobe (usually in ffmpeg package)"

FF_IN=()
if [[ -n "${DURATION:-}" ]]; then
  FF_IN+=(-t "$DURATION")
fi
FF_IN+=(-i "$IN")

# Fill 240x135 then center-crop (FFmpeg 7: avoid scale+pad).
ffmpeg -y "${FF_IN[@]}" \
  -map 0:v -vf "scale=240:135:force_original_aspect_ratio=increase,crop=240:135" -r 15 -q:v 8 "$OUT_V"

echo "Wrote: $OUT_V"

# Second pass: raw PCM only if an audio stream exists. Use first track only — raw u8 muxer rejects multiple audio streams.
if ffprobe -v error -select_streams a -show_entries stream=index -of csv=p=0 "$IN" | grep -q '[0-9]'; then
  ffmpeg -y "${FF_IN[@]}" \
    -map 0:a:0 -f u8 -acodec pcm_u8 -ar 44100 -ac 1 "$OUT_A"
  echo "Wrote: $OUT_A (audio)"
else
  rm -f "$OUT_A"
  echo "No audio stream in file — video-only (no .pcm)"
fi
echo "Copy video.mjpeg (and video.pcm if present) to SD root; eject safely."
