#!/usr/bin/env python3
import sys
import zlib
import struct
import argparse
import os
from util_uf2 import *
from util_asm import *

def calculate_crc32(contents):
    """
    Calculates the CRC32 of a bytearray.
    @param[in] contents Bytearray (e.g. from reading a file) to calculate the CRC32 on.
    @retval CRC32 calculated from contents.
    """
    # Calculate CRC32 of the existing content
    return zlib.crc32(contents) & 0xFFFFFFFF

def append_crc32_bin(filename):
   # Read the binary file
    with open(filename, 'rb') as f:
        contents = f.read()

    crc = calculate_crc32(contents)
    
    # Append the CRC32 as little-endian (RP2040 is little-endian)
    with open(filename, 'wb') as f:
        f.write(contents)
        f.write(struct.pack('<I', crc))
    
    print(f"Appended CRC32: 0x{crc:08X}")
    return crc

def create_header_bin_contents(app_len_bytes, app_crc, status_valid=False):
    """
    Create a bytearray with the contents of a flash partition header.
    @param[in] app_len_bytes Length of the application binary. Used to populate the length field in the header.
    @param[in] app_crc CRC32 of the application binary. Used to populate the crc field in the header.
    @param[in] status_valid Whether to force the status word to be kFlashPartitionStatusValid. Mark this TRUE for
    firmware that we won't verify before booting (e.g. firmware loaded by debugger). Mark this FALSE for firmware
    loaded via OTA updates that will need to be verified before booting.
    @retval Bytearray with contents of header.
    """
    HEADER_VERSION = 0
    HEADER_SIZE_BYTES = 5*4

    status = 0xFFFFFFFF # Default to kFlashPartitionStatusBlank.
    if status_valid:
        status = 0xFFADFFFF # Force kFlashPartitionStatusValid (avoids checksum verification).

    hdr_bin_contents = bytearray(HEADER_SIZE_BYTES)
    struct.pack_into('<I', hdr_bin_contents, 0, 0xAD5BEEE) # MAGIC_WORD: Marks beginning of application header.
    struct.pack_into('<I', hdr_bin_contents, 4, HEADER_VERSION) # HEADER_VERSION: Version of this header schema.
    struct.pack_into('<I', hdr_bin_contents, 8, app_len_bytes) # LEN_BYTES: Application image length in  Bytes.
    struct.pack_into('<I', hdr_bin_contents, 12, app_crc) # CRC: CRC32 of application data.
    struct.pack_into('<I', hdr_bin_contents, 16, status) # STATUS: Application CRC check and boot priority.
    
    return hdr_bin_contents


def generate_header(app_bin_filename, asm_section=None, ota_filename=None):
    """
    Generate a header binary and corresponding assembly file which includes the following:
        0xAD5BEEE
        header_version (uint32_t)
        app_size_bytes (uint32_t)
        app_crc (uint32_t)
        status (uint32_t)
    """
    # application.bin includes a 256-Byte stage 2 bootloader to amke it bootable on its own.
    # Remove this when creating the OTA file, since it's already baked into the bootloader binary.
    STAGE_2_BOOTLOADER_LEN_BYTES = 256

    print(f"Generating header for {app_bin_filename}")

    with open(app_bin_filename, 'rb') as f:
        app_bin_contents = f.read()
    app_bin_contents = app_bin_contents[STAGE_2_BOOTLOADER_LEN_BYTES:]
    print(f"\tapp_bin_contents: " + ", ".join([f"{app_bin_contents[i]:x}" for i in range(10)]) + "..." + ", ".join([f"{app_bin_contents[i]:x}" for i in range(-11,-1)]))
    
    app_crc = calculate_crc32(app_bin_contents)
    print(f"\tCalculated CRC32 for {app_bin_filename} ({len(app_bin_contents)} Bytes): 0x{app_crc:x}")

    # Create a header with the status Byte forced to valid to skip the CRC check in the bootloader
    # (header CRC from application.bin does not match the CRC calculated from the contents flashed by combined.elf).
    hdr_bin_contents = create_header_bin_contents(len(app_bin_contents), app_crc, status_valid=True)

    # app_bin_basename = os.path.splitext(os.path.basename(app_bin_filename))[0]
    app_bin_dir = os.path.dirname(app_bin_filename)
    hdr_bin_filename = os.path.join(app_bin_dir, f"{asm_section}.bin")
    hdr_asm_filename = os.path.join(app_bin_dir, f"{asm_section}.S")

    print(f"\tWriting {len(hdr_bin_contents)} Bytes to {hdr_bin_filename}.")
    with open(hdr_bin_filename, 'wb') as f:
        f.write(hdr_bin_contents)
    
    if asm_section is not None:
        print(f"\tConverting header file to assembly as {hdr_asm_filename}.")
        bin_file_to_asm_file(hdr_bin_filename, hdr_asm_filename, asm_section)
    
    if ota_filename is not None:
        # Don't mark header as valid for OTA files in order to force a checksum validation before booting.
        ota_hdr_bin_contents = create_header_bin_contents(len(app_bin_contents), app_crc, status_valid=False)
        with open(ota_filename, 'wb') as f:
            f.write(ota_hdr_bin_contents)
            f.write(app_bin_contents)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="CRC tools.")
    parser.add_argument("filename")
    parser.add_argument("--header", help="Generate a binary header, then turn it into an assembly header with the provided section name.")
    parser.add_argument("--ota", help="Generate a .ota file that combines the header and application binary.")

    args = parser.parse_args()

    if args.header:
        # Generate header binary and assembly files.
        generate_header(args.filename, args.header, args.ota)
    else:
        # Just calculate CRC of a binary.
        with open(args.filename, 'rb') as f:
            contents = f.read()
        print(f"Calculated CRC32: 0x{calculate_crc32(contents):x}")
    