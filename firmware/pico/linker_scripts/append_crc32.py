#!/usr/bin/env python3
import sys
import zlib
import struct
from uf2_tools import *

def append_crc32_bin(filename):
    # Read the binary file
    with open(filename, 'rb') as f:
        contents = f.read()
    
    # Calculate CRC32 of the existing content
    crc = zlib.crc32(contents) & 0xFFFFFFFF
    
    # Append the CRC32 as little-endian (RP2040 is little-endian)
    with open(filename, 'wb') as f:
        f.write(contents)
        f.write(struct.pack('<I', crc))
    
    print(f"Appended CRC32: 0x{crc:08X}")
    return crc



def append_crc_uf2(filename):
    with open(filename, 'rb') as f:
        uf2_data = f.read()

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: append_crc.py <firmware.bin> <firmware.uf2>")
        sys.exit(1)
    
    append_crc32_bin(sys.argv[1])
    append_crc_uf2(sys.argv[2])