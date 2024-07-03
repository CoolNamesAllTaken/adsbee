#!/bin/bash

# This script uses the xxd utility in Linux to package the build output of the esp32 firmware into a .h file that can
# subsequently be included in the RP2040 firmware.

script_dir=$(dirname $0)
esp_firmware_bin_file=$script_dir/esp_bin/adsbee_esp.bin
esp_firmware_header_file=$script_dir/esp_bin/esp_firmware.h

echo "Converting $esp_firmware_bin_file -> $esp_firmware_header_file"

# Check if xxd is installed
if ! command -v xxd &> /dev/null; then
    echo "xxd is not installed. Installing..."
    # Update package list and install xxd
    sudo apt-get update && sudo apt-get install -y xxd
fi

# Convert the 
xxd -i $esp_firmware_bin_file $esp_firmware_header_file

esp_firmware_file_size_bytes=$(stat -c%s $esp_firmware_header_file)
echo "Wrote $esp_firmware_file_size_bytes Bytes to $esp_firmware_header_file"