# ads-bee Firmware

## Prerequisites

### Docker

Install Docker via the official apt repository — **do not use the snap package**, as it has socket permission issues.

### Git Submodules

```bash
git submodule update --init --recursive
```

> **Windows note:** Cloning on Windows may produce files with CR+LF line endings, which break Docker builds. Run `git config --global core.autocrlf false` before cloning.

---

## Build System Overview

The build system uses Docker Compose with three pre-built containers — no local image build is required. Images are pulled automatically on first run.

| Service | Image | Builds |
|---------|-------|--------|
| `pico-docker` | `coolnamesalltaken/pico-docker:latest` | RP2040 firmware, host tests |
| `esp-idf` | `espressif/idf:v5.5.2` | ESP32-S3 firmware |
| `ti-lpf2` | `coolnamesalltaken/ti-lpf2:latest` | TI CC1312 firmware |

The compose file lives at `firmware/adsbee_1090/compose.yml`. The build script handles the required build order (ESP32 → CC1312 → RP2040) automatically.

---

## Building Firmware

Run from the repo root:

```bash
bash firmware/adsbee_1090/build.sh [options] [target]
```

### Targets

| Target | Description |
|--------|-------------|
| `all` (default) | Build all three firmware targets in the correct order |
| `esp` | ESP32-S3 only |
| `ti` | TI CC1312 only |
| `pico` | RP2040 only (requires ESP32 and CC1312 builds to exist first) |
| `test [filter]` | Build and run host unit tests; `filter` is an optional ctest `-R` regex (e.g. `AircraftJSON`) |
| `clean` | Delete all build output directories |

### Options

| Flag | Description |
|------|-------------|
| `-d` | Build in Debug mode (default is Release) |

### Examples

```bash
bash firmware/adsbee_1090/build.sh            # full release build
bash firmware/adsbee_1090/build.sh -d         # full debug build
bash firmware/adsbee_1090/build.sh esp        # ESP32 only
bash firmware/adsbee_1090/build.sh test       # run all host tests
bash firmware/adsbee_1090/build.sh test AircraftJSON  # run filtered tests
```

### Build Output

| Target | Output |
|--------|--------|
| RP2040 (Release) | `firmware/adsbee_1090/pico/build/Release/application/combined.uf2` |
| RP2040 (Debug) | `firmware/adsbee_1090/pico/build/Debug/application/combined.uf2` |
| ESP32 (Release) | `firmware/adsbee_1090/esp/build/Release/adsbee_esp.bin` |
| CC1312 | `firmware/adsbee_1090/ti/sub_ghz_radio/build/sub_ghz_radio.bin` |

The `combined.uf2` embeds all three binaries. See [Developers_Guide.md](adsbee_1090/Developers_Guide.md) for flashing instructions.

---

## Interactive Shell

To open a shell inside a container for debugging or manual builds:

```bash
cd firmware/adsbee_1090
docker compose run --rm pico-docker bash   # RP2040 / test container
docker compose run --rm esp-idf bash       # ESP32 container
docker compose run --rm ti-lpf2 bash       # CC1312 container
```

---

## VS Code Integration

1. Install the **Dev Containers** VS Code extension.
2. Start the target container: `cd firmware/adsbee_1090 && docker compose run --rm pico-docker bash`
3. In VS Code, open the Remote Explorer panel, right-click the running container, and select **Attach to Container**.
4. Inside the attached VS Code, install the **Cortex-Debug** and **C/C++** extensions.
5. Use **Open Folder** to navigate to `/firmware/adsbee_1090` to pick up the `.vscode/launch.json` debug configuration.

---

## Removing Docker Images

```bash
docker image rm coolnamesalltaken/pico-docker:latest
docker image rm espressif/idf:v5.5.2
docker image rm coolnamesalltaken/ti-lpf2:latest
```
