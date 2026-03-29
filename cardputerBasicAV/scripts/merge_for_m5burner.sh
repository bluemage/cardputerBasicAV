#!/usr/bin/env bash
# OPTIONAL — only if you build with PlatformIO (`pio run`). If you use Arduino IDE,
# follow docs/M5BURNER.md and run `esptool merge_bin` yourself (no script needed).
#
# Merge bootloader + partition table + app into one .bin for M5Burner "User Custom".
#
# Usage (from project root, after `pio run`):
#   ./scripts/merge_for_m5burner.sh
#
# Optional: PIO_ENV=m5cardputer-adv ./scripts/merge_for_m5burner.sh
#
# Flash the output from M5Burner → User Custom → (Flash / Publish with local file).

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ENV_NAME="${PIO_ENV:-m5cardputer-adv}"
BUILD="${ROOT}/.pio/build/${ENV_NAME}"
OUT_DIR="${ROOT}/firmware"
OUT_BIN="${OUT_DIR}/cardputerBasicAV_m5burner.bin"

die() { echo "error: $*" >&2; exit 1; }

[[ -d "$BUILD" ]] || die "build dir missing: $BUILD — run: pio run"

for f in bootloader.bin partitions.bin boot_app0.bin firmware.bin; do
  [[ -f "${BUILD}/${f}" ]] || die "missing ${BUILD}/${f} — run: pio run"
done

# Match m5stack-stamps3: QIO, 80 MHz, 8 MB (see board JSON in platform-espressif32).
FLASH_MODE="qio"
FLASH_FREQ="80m"
FLASH_SIZE="8MB"

mkdir -p "$OUT_DIR"

if command -v pio >/dev/null 2>&1; then
  ( cd "$ROOT" && pio pkg exec -e "$ENV_NAME" -- python -m esptool --chip esp32s3 merge_bin \
    -o "$OUT_BIN" \
    --flash_mode "$FLASH_MODE" \
    --flash_freq "$FLASH_FREQ" \
    --flash_size "$FLASH_SIZE" \
    0x0 "${BUILD}/bootloader.bin" \
    0x8000 "${BUILD}/partitions.bin" \
    0xe000 "${BUILD}/boot_app0.bin" \
    0x10000 "${BUILD}/firmware.bin" )
elif python3 -m esptool version >/dev/null 2>&1; then
  python3 -m esptool --chip esp32s3 merge_bin \
  -o "$OUT_BIN" \
  --flash_mode "$FLASH_MODE" \
  --flash_freq "$FLASH_FREQ" \
  --flash_size "$FLASH_SIZE" \
  0x0 "${BUILD}/bootloader.bin" \
  0x8000 "${BUILD}/partitions.bin" \
  0xe000 "${BUILD}/boot_app0.bin" \
  0x10000 "${BUILD}/firmware.bin"
else
  die "install PlatformIO (pio) and run from project root, or: pip install esptool"
fi

echo "Wrote $OUT_BIN"
echo "In M5Burner: User Custom → add/flash this file; pick M5 Cardputer ADV (Stamp S3) if prompted."
