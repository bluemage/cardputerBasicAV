# One file to flash in M5Burner (Ubuntu)

**Hardware this project targets: M5Stack Cardputer ADV** (ESP32-S3, ES8311 audio). Pick the matching board profile in Arduino IDE / M5Burner.

## What you actually need

M5Burner flashes a **single “full flash” `.bin`** (bootloader + partition table + your app glued together). That file is **not** something M5Stack hosts for this project; it is **created on your PC** when you **compile** the sketch.

You do **not** need **PlatformIO** (`pio`) or anything in the **`scripts/`** folder unless you already use them. Those are optional shortcuts for developers.

---

## Easiest path: Arduino IDE + one terminal command (Ubuntu)

### 1. Install Arduino IDE and M5 support

- Install [Arduino IDE 2](https://www.arduino.cc/en/software) (or 1.8.x).
- Add the ESP32 board package (M5’s [Cardputer programming guide](https://docs.m5stack.com/en/arduino/m5cardputer/program) has the board URL and steps).
- Install the **M5Cardputer** library from the Library Manager (and dependencies it asks for).

### 2. Open this sketch and compile

- Open **`cardputerBasicAV.ino`** (same folder as this `docs/` directory).
- Board: **M5Cardputer** package → choose the profile for **Cardputer ADV** (not assumed to match the original Cardputer without checking).
- Click **Verify** (check mark) so the build succeeds.

### 3. Find the build folder (where the `.bin` pieces are)

1. **File → Preferences** → enable **verbose output** during **compilation**.
2. Click **Verify** again.
3. In the **Output** panel at the bottom, search for **`bootloader.bin`**. The log line will contain a **full path** to that file (and the other binaries live in the **same directory**).

That directory should contain, among other things:

- A bootloader (often **`SKETCH.ino.bootloader.bin`** in Arduino IDE 2, or `bootloader.bin` in some setups)
- Partition table (**`SKETCH.ino.partitions.bin`** or `partitions.bin`)
- **`boot_app0.bin`**
- Your app: **`SKETCH.ino.bin`**
- **`SKETCH.ino.merged.bin`** (Arduino IDE 2 / ESP32 core often writes this — see step 5)

Open **`flash_args`** in that same folder: it lists the exact **flash mode, size, and addresses** the core used for your board (use those values if you run `merge_bin` manually).

Remember that folder path; call it `BUILD_DIR` below.

### 4. Install `esptool` on Ubuntu

```bash
sudo apt update
sudo apt install esptool
```

(If `esptool` is not in your Ubuntu version, use `pip install esptool` and run `python3 -m esptool` instead of `esptool` in the next step.)

### 5. One `.bin` file for M5Burner

#### Option A — use the merged file Arduino already built (simplest)

After **Verify**, if you see **`cardputerBasicAV.ino.merged.bin`** in `BUILD_DIR` (often **4 MB** for a 4 MB flash profile), that file is **already** bootloader + partitions + `boot_app0` + app, padded for flashing.

Copy it somewhere handy and select it in **M5Burner → User Custom**:

```bash
cp "BUILD_DIR/cardputerBasicAV.ino.merged.bin" "$HOME/cardputerBasicAV_m5burner.bin"
```

Use **`$HOME/cardputerBasicAV_m5burner.bin`** in M5Burner. No `esptool merge_bin` required.

#### Option B — merge the four pieces yourself (same result)

Use **`flash_args`** in `BUILD_DIR` for `--flash_mode` and `--flash_size` (your build might say **`dio`** and **`4MB`**, not 8 MB / QIO). Chip for M5 Cardputer is **ESP32-S3**:

```bash
cd "$HOME/cardputer/cardputerBasicAV/build/m5stack.esp32.m5stack_cardputer"

python3 -m esptool --chip esp32s3 merge_bin \
  -o "$HOME/cardputerBasicAV_m5burner.bin" \
  --flash_mode dio --flash_freq 80m --fill-flash-size 4MB \
  0x0 cardputerBasicAV.ino.bootloader.bin \
  0x8000 cardputerBasicAV.ino.partitions.bin \
  0xe000 boot_app0.bin \
  0x10000 cardputerBasicAV.ino.bin
```

Adjust the **`cd`** path if your `BUILD_DIR` differs. Use **`--fill-flash-size`** with the same size as **`flash_args`** (here **4MB**) so the file matches **`*.ino.merged.bin`** (~4,194,304 bytes); without it, **esptool v4** may write a short image only. If **`python3 -m esptool`** is unavailable, install **`esptool`** (`apt` or `pip`) and use the same flags with the **`esptool`** command if it is on your `PATH`.

**PlatformIO** builds (this repo’s `pio run`) often use **8 MB / QIO**; use **`scripts/merge_for_m5burner.sh`** for that path instead of copying the Arduino `flash_args` line blindly.

---

## Flash with M5Burner on Ubuntu

- Install **M5Burner for Linux** from the [M5Stack download page](https://docs.m5stack.com/en/download) (often an **AppImage**: `chmod +x` then run it).
- Add your user to **`dialout`** so USB serial works, then log out and back in:

  ```bash
  sudo usermod -aG dialout "$USER"
  ```

- With the Cardputer plugged in, you usually see **`/dev/ttyACM0`** (pick that in M5Burner if it appears).

---

## Optional: `scripts/` and `platformio.ini`

- **`scripts/merge_for_m5burner.sh`** only helps if you build with **PlatformIO** (`pio run`). It runs the same **`esptool merge_bin`** idea as step 5 above. **Ignore it** if you use Arduino IDE only.
- **`platformio.ini`** is for people who use PlatformIO instead of Arduino IDE.

---

## What M5Burner “Firmware Exporter” is

**Firmware Exporter** saves a **copy of flash from a device** that is already running firmware. It does **not** build this project. For this app, you want **compile → merge → flash** as above.

---

## If merge fails

- Match **`--flash_mode`**, **`--flash_freq`**, and **`--flash_size`** to **`flash_args`** in your `BUILD_DIR` (Arduino may use **4 MB** and **dio**; PlatformIO in this repo uses **8 MB** / **qio**).
- Confirm all four input files came from the **same** successful build (same `BUILD_DIR`).
- If bootloader or partition files have different names, use the names in **`flash_args`** (or prefer **Option A** and flash **`*.ino.merged.bin`**).
