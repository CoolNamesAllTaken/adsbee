#!/bin/bash
# ADSBee firmware build script.
# Builds all three firmware targets (ESP32, TI CC1312, RP2040 Pico) using Docker containers.
# Usage: ./build.sh [-d] [target] [test_filter]
#   targets: all (default), esp, ti, pico, test, clean
#   -d: build in Debug mode instead of Release
#   test_filter: optional regex passed to ctest -R when target is "test" (e.g. "AircraftJSON")

set -e

script_dir="$(cd "$(dirname "$0")" && pwd)"
cd "$script_dir"

# Number of parallel build jobs.
jobs=$(nproc 2>/dev/null || echo 4)
required_esp_idf_version="v5.5.2"

debug=false
if [ "$1" = "-d" ]; then
    debug=true
    shift
fi
test_filter="${2:-}"

# Verify the Settings/firmware version sync rule (see firmware/scripts/check_version_sync.sh).
# Compares the committed state (HEAD) against the working tree.
check_version_sync() {
    "$script_dir/../scripts/check_version_sync.sh" HEAD WORKTREE
}

check_esp_idf_version() {
    echo "=== Checking ESP-IDF version (required: $required_esp_idf_version) ==="
    local idf_version
    idf_version=$(docker compose run --rm esp-idf bash -c "idf.py --version")
    echo "ESP-IDF reported by container: $idf_version"
    if [[ "$idf_version" != *"$required_esp_idf_version"* ]]; then
        echo "ERROR: ESP-IDF version mismatch. Expected $required_esp_idf_version."
        echo "Update compose.yml to pin the esp-idf image tag to $required_esp_idf_version."
        exit 1
    fi
}

build_esp() {
    check_esp_idf_version
    if [ "$debug" = true ]; then
        echo "=== Building ESP32-S3 firmware (Debug) ==="
        # sdkconfig_debug is auto-generated on first run by layering sdkconfig.debug on top of sdkconfig.
        # Delete esp/sdkconfig_debug to force regeneration (e.g. after base sdkconfig changes).
        docker compose run --rm esp-idf bash -c "
            cd /firmware/adsbee_1090/esp &&
            idf.py -B build/Debug -D CMAKE_BUILD_TYPE=Debug -D SDKCONFIG=\"\$(pwd)/sdkconfig_debug\" -D \"SDKCONFIG_DEFAULTS=\$(pwd)/sdkconfig;\$(pwd)/sdkconfig.debug\" build
        "
        echo "=== ESP32-S3 build complete (Debug): esp/build/Debug/adsbee_esp.bin ==="
    else
        echo "=== Building ESP32-S3 firmware ==="
        docker compose run --rm esp-idf bash -c "
            cd /firmware/adsbee_1090/esp &&
            idf.py -B build/Release build
        "
        echo "=== ESP32-S3 build complete: esp/build/Release/adsbee_esp.bin ==="
    fi
}

build_ti() {
    local build_type=$( [ "$debug" = true ] && echo "Debug" || echo "Release" )
    echo "=== Building TI CC1312 firmware ($build_type) ==="
    docker compose run --rm ti-lpf2 bash -c "
        cd /firmware/adsbee_1090/ti/sub_ghz_radio &&
        mkdir -p build && cd build &&
        cmake -DCMAKE_BUILD_TYPE=$build_type \
              -DCMAKE_C_COMPILER=/usr/bin/arm-none-eabi-gcc \
              -DCMAKE_CXX_COMPILER=/usr/bin/arm-none-eabi-g++ .. &&
        cmake --build . --config $build_type --target all -j $jobs
    "
    echo "=== TI CC1312 build complete: ti/sub_ghz_radio/build/sub_ghz_radio.bin ==="
}

build_pico() {
    local build_type=$( [ "$debug" = true ] && echo "Debug" || echo "Release" )
    echo "=== Building RP2040 Pico firmware ($build_type) ==="
    # Check that ESP32 and TI firmware exist.
    local esp_build_dir=$( [ "$debug" = true ] && echo "esp/build/Debug" || echo "esp/build/Release" )
    if [ ! -f $esp_build_dir/adsbee_esp.bin ]; then
        echo "ERROR: $esp_build_dir/adsbee_esp.bin not found. Run ESP32 build first."
        exit 1
    fi
    if [ ! -f ti/sub_ghz_radio/build/sub_ghz_radio.bin ]; then
        echo "ERROR: ti/sub_ghz_radio/build/sub_ghz_radio.bin not found. Run TI build first."
        exit 1
    fi
    docker compose run --rm pico-docker bash -c "
        cd /firmware/adsbee_1090/pico &&
        mkdir -p build/$build_type && cd build/$build_type &&
        cmake -DCMAKE_BUILD_TYPE=$build_type \
              -DCMAKE_C_COMPILER=/usr/bin/arm-none-eabi-gcc \
              -DCMAKE_CXX_COMPILER=/usr/bin/arm-none-eabi-g++ ../.. &&
        cmake --build . --config $build_type --target all -j $jobs
    "
    echo "=== RP2040 Pico build complete ==="
    echo "  Firmware: pico/build/$build_type/application/combined.uf2"
    echo "  OTA:      pico/build/$build_type/application/adsbee_1090.ota"
}

build_test() {
    local filter="${1:-}"
    local ctest_filter_opt=""
    if [ -n "$filter" ]; then
        ctest_filter_opt="-R $filter"
        echo "=== Building and running host tests (filter: $filter) ==="
    else
        echo "=== Building and running host tests ==="
    fi
    docker compose run --rm pico-docker bash -c "
        cd /firmware/modules/googletest &&
        mkdir -p build && cd build &&
        cmake -DBUILD_SHARED_LIBS=ON .. &&
        make -j $jobs &&
        cd /firmware/adsbee_1090/pico &&
        mkdir -p build/Test && cd build/Test &&
        cmake -DCMAKE_BUILD_TYPE=Test \
              -DCMAKE_C_COMPILER=/usr/bin/gcc \
              -DCMAKE_CXX_COMPILER=/usr/bin/g++ ../.. &&
        make -j $jobs &&
        ctest --verbose $ctest_filter_opt
    "
    echo "=== Host tests complete ==="
}

clean_builds() {
    echo "=== Cleaning build directories ==="
    rm -rf esp/build
    rm -rf esp/sdkconfig_debug
    rm -rf ti/sub_ghz_radio/build
    rm -rf pico/build
    echo "=== Clean complete ==="
}

target="${1:-all}"

if [ "$target" != "clean" ]; then
    check_version_sync
fi

case "$target" in
    esp)
        build_esp
        ;;
    ti)
        build_ti
        ;;
    pico)
        build_pico
        ;;
    test)
        build_test "$test_filter"
        ;;
    clean)
        clean_builds
        ;;
    all)
        build_type=$( [ "$debug" = true ] && echo "Debug" || echo "Release" )
        build_esp
        build_ti
        build_pico
        echo ""
        echo "=== Full build complete! ==="
        echo "  Output: firmware/pico/build/$build_type/application/combined.uf2"
        ;;
    *)
        echo "Usage: $0 [-d] [esp|ti|pico|test|clean|all]"
        echo "  -d    - Build in Debug mode instead of Release"
        echo "  all   - Build all firmware targets (default)"
        echo "  esp   - Build ESP32-S3 firmware only"
        echo "  ti    - Build TI CC1312 firmware only"
        echo "  pico  - Build RP2040 Pico firmware only (requires esp + ti first)"
        echo "  test [filter] - Build and run host unit tests; optional filter is a ctest -R regex (e.g. \"AircraftJSON\")"
        echo "  clean - Remove all build directories"
        exit 1
        ;;
esac
