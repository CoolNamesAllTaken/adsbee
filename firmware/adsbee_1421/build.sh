#!/bin/bash
# ADSBee 1421 firmware build script.
# Builds an application inside the Docker container that owns its toolchain (defined in
# compose.yml) -- the toolchains only exist inside those containers.
#
# Usage: ./build.sh [-d] [clean] [app]
#   app         ti (default, CC1314R10 application via ti-lpf2)
#               programmer (RP2040-Zero flash/passthrough jig via pico-docker;
#                           requires ti to be built first)
#   (default)   build in Release
#   -d          build in Debug instead of Release
#   clean       remove <app>/build and exit

set -euo pipefail

# Always run from the directory containing compose.yml so `docker compose` finds it.
cd "$(dirname "$0")"

APP="ti"
CONFIG="Release"
DO_CLEAN=0

for arg in "$@"; do
    case "$arg" in
        -d) CONFIG="Debug" ;;
        clean) DO_CLEAN=1 ;;
        ti|programmer) APP="$arg" ;;
        -h|--help)
            sed -n '2,12p' "$0"
            exit 0
            ;;
        *)
            echo "Unknown argument: $arg" >&2
            sed -n '2,12p' "$0" >&2
            exit 1
            ;;
    esac
done

# Each app names the container that holds its toolchain, the artifact base name, and the
# artifact extensions it emits.
EXTRA_CMAKE_ARGS=""
case "$APP" in
    ti)
        SERVICE="ti-lpf2"
        ARTIFACT="adsbee_1421"
        ARTIFACT_EXTS=(elf hex map)
        ;;
    programmer)
        SERVICE="pico-docker"
        ARTIFACT="adsbee_1421_programmer"
        ARTIFACT_EXTS=(uf2 elf)
        # picotool is not installed in the image, and the Pico SDK builds it from source to make
        # .uf2 files. Cache it outside build/ so `clean` does not force another download+build.
        EXTRA_CMAKE_ARGS="-DPICOTOOL_FETCH_FROM_GIT_PATH=/firmware/adsbee_1421/.picotool"
        ;;
esac

if [ "$DO_CLEAN" -eq 1 ]; then
    echo "Removing ${APP}/build ..."
    rm -rf "${APP}/build"
    echo "Clean complete."
    exit 0
fi

# Verify the Settings/firmware version sync rule (see firmware/scripts/check_version_sync.sh).
# Compares the committed state (HEAD) against the working tree. Advisory only: a failure warns
# and the build continues. The pre-commit hook installed by scripts/setup_dev.sh is the hard gate.
# `set -e` does not apply to a command in an `if` condition, so this cannot abort the build.
if ! "$(pwd)/../scripts/check_version_sync.sh" HEAD WORKTREE; then
    echo ""
    echo "WARNING: version sync check failed (see above). Continuing with the build anyway."
    echo "         Firmware is only reflashed on a version mismatch, so a device flashed with"
    echo "         this build may keep running stale firmware."
    echo ""
fi

echo "Building ${APP} (${CONFIG}) in container ${SERVICE} ..."

# Keep the toolchain container running so incremental rebuilds reuse the CMake cache.
docker compose up -d "${SERVICE}"

# Configure + build inside the container. The CMake ADSBEE_*_DIR defaults resolve to
# /firmware/common and /firmware/modules via the compose.yml volume mounts (and to
# firmware/common and firmware/modules on the host), so no overrides are needed.
docker compose exec "${SERVICE}" bash -c "
    set -e
    cd /firmware/adsbee_1421/${APP}
    mkdir -p build/${CONFIG}
    cd build/${CONFIG}
    cmake -DCMAKE_BUILD_TYPE=${CONFIG} \
          -DCMAKE_C_COMPILER=/usr/bin/arm-none-eabi-gcc \
          -DCMAKE_CXX_COMPILER=/usr/bin/arm-none-eabi-g++ ${EXTRA_CMAKE_ARGS} ../..
    cmake --build . --config ${CONFIG} --target all -j \$(nproc)
"

echo ""
echo "Build complete. Artifacts:"
OUT="${APP}/build/${CONFIG}"
# Both the stable names (adsbee_1421.hex) and CMake's version-stamped copies
# (adsbee_1421-0.3.6.hex) are produced, so glob to list them all.
for ext in "${ARTIFACT_EXTS[@]}"; do
    for f in "${OUT}/${ARTIFACT}"*".${ext}"; do
        [ -f "$f" ] && echo "  $f"
    done
done
