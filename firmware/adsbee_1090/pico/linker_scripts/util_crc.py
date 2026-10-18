#!/usr/bin/env python3
import sys
import zlib
import struct
import argparse
import os
import subprocess
import tempfile
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


def generate_header(app_bin_filenames, asm_section=None, ota_filename=None):
    """
    Generate a header binary and corresponding assembly file which includes the following:
        0xAD5BEEE
        header_version (uint32_t)
        app_size_bytes (uint32_t)
        app_crc (uint32_t)
        status (uint32_t)

    @param[in] app_bin_filenames List of binary filenames to generate headers for.
    @param[in] asm_section Section name to use for the assembly file.
    @param[in] ota_filename Filename to write the OTA file to. If None, no OTA file will be generated.
    """

    print(f"Generating headers for " + ", ".join(app_bin_filenames) + ".")

    # List of bytearrays to hold header and OTA app binary contents for each partition.
    ota_partition_contents = []

    for i in range(len(app_bin_filenames)):
        app_bin_filename = app_bin_filenames[i]
        print(f"Reading {app_bin_filename}.")
        if not os.path.exists(app_bin_filename):
            print(f"Error: {app_bin_filename} does not exist.")
            sys.exit(1)
        with open(app_bin_filename, 'rb') as f:
            app_bin_contents = f.read()
        # print(f"\tapp_bin_contents: " + ", ".join([f"{app_bin_contents[i]:x}" for i in range(10)]) + "..." + ", ".join([f"{app_bin_contents[i]:x}" for i in range(-11,-1)]))
    
        app_crc = calculate_crc32(app_bin_contents)
        print(f"\tCalculated CRC32 for {app_bin_filename} ({len(app_bin_contents)} Bytes): 0x{app_crc:x}")

        app_bin_dir = os.path.dirname(app_bin_filename)

        # Special case: assume the first application binary is used for debugging, so we should create an assembly file
        # for it with the CRC check skipped.
        if i == 0:
            hdr_bin_filename = os.path.join(app_bin_dir, f"{asm_section}.bin")
            hdr_asm_filename = os.path.join(app_bin_dir, f"{asm_section}.S")
            # Create a header with the status Byte forced to valid to skip the CRC check in the bootloader. This is a
            # placeholder: patch_elf_header() replaces it with the header of the image combined.elf actually contains.
            hdr_bin_contents = create_header_bin_contents(len(app_bin_contents), app_crc, status_valid=True)

            print(f"\tWriting {len(hdr_bin_contents)} Bytes to {hdr_bin_filename}.")
            with open(hdr_bin_filename, 'wb') as f:
                f.write(hdr_bin_contents)
    
            if asm_section is not None:
                print(f"\tConverting header file to assembly as {hdr_asm_filename}.")
                bin_file_to_asm_file(hdr_bin_filename, hdr_asm_filename, asm_section)
    
        # Don't mark header as valid for OTA files in order to force a checksum validation before booting.
        ota_hdr_bin_contents = create_header_bin_contents(len(app_bin_contents), app_crc, status_valid=False)
        ota_partition_contents.append(ota_hdr_bin_contents + app_bin_contents)

    # Package the header and application binaries for each partition into an OTA file.
    if ota_filename is not None:
        # OTA File Contents:
        #   NUM_PARTITIONS (4 Bytes)
        #   PARTITION_0_0FFSET (4 Bytes)
        #   PARTITION_1_OFFSET (4 Bytes)
        #   PARTITION 0 HEADER (4 Bytes)
        #   PARTITION 0 APP (4 Bytes)
        #   PARTITION 1 HEADER (4 Bytes)
        #   PARTITION 1 APP (4 Bytes)

        ota_file_contents = bytearray(4)
        num_partitions = len(ota_partition_contents)
        print(f"Writing {num_partitions} partitions to {ota_filename}.")
        struct.pack_into('<I', ota_file_contents, 0, num_partitions)
        partition_lengths = [len(part) for part in ota_partition_contents]
        # Add array of offsets.
        current_offset = 4 + 4*num_partitions
        for i in range(num_partitions):
            print(f"\tPartition {i} offset: {current_offset} Bytes.")
            ota_file_contents.extend(struct.pack('<I', current_offset))
            current_offset += partition_lengths[i]
        # Add array of partition headers and app binaries.
        for i in range(num_partitions):
            ota_file_contents.extend(ota_partition_contents[i])
            
        with open(ota_filename, 'wb') as f:
            f.write(ota_file_contents)


def patch_elf_header(elf_filename, objcopy, section, app_offset):
    """
    Rewrite the partition header section of an ELF to describe the application the ELF itself contains. The combined
    image is linked separately from app0.bin, so the header generated for app0.bin doesn't match it.
    @param[in] elf_filename ELF with a bootloader, a partition header section and an application, linked from the
    start of flash.
    @param[in] objcopy Path to the toolchain's objcopy.
    @param[in] section Name of the header section, e.g. ".hdr0".
    @param[in] app_offset Offset of the application from the start of flash.
    @retval Header contents written to the ELF.
    """
    with tempfile.TemporaryDirectory() as tmp_dir:
        flat_filename = os.path.join(tmp_dir, "flat.bin")
        hdr_filename = os.path.join(tmp_dir, "hdr.bin")
        subprocess.run([objcopy, "-O", "binary", elf_filename, flat_filename], check=True)
        with open(flat_filename, 'rb') as f:
            app_bin_contents = f.read()[app_offset:]
        if not app_bin_contents:
            print(f"Error: {elf_filename} has no application at offset 0x{app_offset:x}.")
            sys.exit(1)
        app_crc = calculate_crc32(app_bin_contents)
        hdr_bin_contents = create_header_bin_contents(len(app_bin_contents), app_crc, status_valid=True)
        with open(hdr_filename, 'wb') as f:
            f.write(hdr_bin_contents)
        subprocess.run([objcopy, "--update-section", f"{section}={hdr_filename}", elf_filename], check=True)
    print(f"Patched {section} of {elf_filename}: {len(app_bin_contents)} Bytes, CRC32 0x{app_crc:x}.")
    return hdr_bin_contents


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="CRC tools.")
    parser.add_argument("filenames", nargs='+', help="List of binary filenames.")
    parser.add_argument("--header", help="Generate a binary header, then turn it into an assembly header with the provided section name.")
    parser.add_argument("--ota", help="Generate a .ota file that combines the header and application binary.")
    parser.add_argument("--patch-elf-header", metavar="SECTION",
                        help="Rewrite this header section of the ELF given as filename to describe its own application.")
    parser.add_argument("--objcopy", default="arm-none-eabi-objcopy", help="objcopy for --patch-elf-header.")
    parser.add_argument("--app-offset", type=lambda x: int(x, 0), default=0x2D000,
                        help="Application offset from the start of flash for --patch-elf-header.")

    args = parser.parse_args()

    if args.patch_elf_header:
        patch_elf_header(args.filenames[0], args.objcopy, args.patch_elf_header, args.app_offset)
    elif args.header:
        # Generate header binary and assembly files.
        generate_header(args.filenames, args.header, args.ota)
    else:
        # Just calculate CRC of a binary.
        with open(args.filename, 'rb') as f:
            contents = f.read()
        print(f"Calculated CRC32: 0x{calculate_crc32(contents):x}")
    