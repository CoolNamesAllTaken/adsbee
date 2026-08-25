#!/bin/bash
# Shared helpers for flashing RP2040 targets over the UF2 mass-storage bootloader.
#
# The RP2040 does not expose the USB DFU class, so dfu-util does not apply. Its bootloader
# enumerates as the RPI-RP2 mass-storage drive; flashing means copying a .uf2 onto it.
#
# Source this from a board's build.sh:
#     source "$(dirname "$0")/../scripts/uf2_flash_lib.sh"

# Prints the RPI-RP2 UF2 bootloader mount point if one is present (macOS and Linux layouts).
find_rpi_drive() {
    local user="${USER:-$(id -un)}"
    local d
    for d in /Volumes/RPI-RP2 /media/RPI-RP2 "/media/${user}/RPI-RP2" "/run/media/${user}/RPI-RP2"; do
        if [ -d "$d" ]; then
            echo "$d"
            return 0
        fi
    done
    return 1
}

# Lists candidate USB CDC serial nodes (macOS /dev/cu.usbmodem*, Linux /dev/ttyACM*).
list_serial_nodes() {
    ls /dev/cu.usbmodem* /dev/ttyACM* 2>/dev/null || true
}

# wait_for_rpi_drive <timeout_s>
# Polls once a second for the RPI-RP2 drive; prints its path on success, returns 1 on timeout.
wait_for_rpi_drive() {
    local timeout="${1:-120}"
    local drive="" i
    for i in $(seq 1 "$timeout"); do
        if drive="$(find_rpi_drive)"; then
            echo "$drive"
            return 0
        fi
        sleep 1
    done
    return 1
}

# copy_uf2_and_confirm <uf2> <drive>
# Copies the image and confirms the bootloader accepted it. Returns 1 if the drive is still
# mounted afterwards (i.e. the uf2 was rejected).
copy_uf2_and_confirm() {
    local uf2="$1" drive="$2" i

    echo "Found ${drive}; copying $(basename "$uf2") ..."
    # The RP2040 reboots as soon as the last uf2 block lands, which can make the volume vanish mid
    # syscall -- treat cp/sync errors as benign and use the drive's disappearance as the real signal.
    cp "$uf2" "${drive}/" 2>/dev/null || true
    sync 2>/dev/null || true

    for i in $(seq 1 15); do
        if ! find_rpi_drive >/dev/null; then
            return 0
        fi
        sleep 1
    done
    return 1
}
