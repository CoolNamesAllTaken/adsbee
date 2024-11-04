import struct
import math # for ceil
from typing import List
import argparse
import os

class UF2Block:
    # UF2 Specification: https://github.com/microsoft/uf2
    UF2_BLOCK_SIZE_BYTES = 512
    UF2_PAYLOAD_MAX_SIZE_BYTES = 476 # 512 - 32 (header) - 4 (final magic number)
    UF2_HEADER_SIZE_BYTES = 32
    UF2_TAIL_SIZE_BYTES = 4
    UF2_MAGIC_START0 = 0x0A324655
    UF2_MAGIC_START1 = 0x9E5D5157
    UF2_MAGIC_END = 0x0AB16F30

    def __init__(self, block_data:bytearray,
                 flags:int, 
                 address:int,
                 payload_size_bytes:int, 
                 block_number:int, 
                 total_blocks:int, 
                 family_id:int, 
                 payload_data:bytearray
    ):
            self.block_data = block_data

            self.flags = flags
            self.address = address
            self.payload_size_bytes = payload_size_bytes
            self.block_number = block_number
            self.total_blocks = total_blocks
            self.family_id = family_id
            self.payload_data = payload_data


    @classmethod
    def from_block(cls, block_data):
        """
        Create a UF2 block from a binary data block.
        """

        magic_start0 = struct.unpack('<I', block_data[0:4])[0]
        magic_start1 = struct.unpack('<I', block_data[4:8])[0]
        magic_end = struct.unpack('<I', block_data[-4:])[0]
            
        if magic_start0 != cls.UF2_MAGIC_START0:
            raise(Exception(f"Invalid UF2 magic word start0. Expected 0x{cls.UF2_MAGIC_START0:x} but got 0x{magic_start0:x}"))
        if magic_start1 != cls.UF2_MAGIC_START1:
            raise(Exception(f"Invalid UF2 magic word start1. Expected 0x{cls.UF2_MAGIC_START1:x} but got 0x{magic_start1:x}"))
        if magic_end != cls.UF2_MAGIC_END:
            raise(Exception(f"Invalid UF2 magic end. Expected 0x{cls.UF2_MAGIC_END:x} but got 0x{magic_end}"))
        
        # Extract payload
        flags = struct.unpack('<I', block_data[8:12])[0]
        address = struct.unpack('<I', block_data[12:16])[0]
        payload_size_bytes = struct.unpack('<I', block_data[16:20])[0]
        block_number = struct.unpack('<I', block_data[20:24])[0]
        total_blocks = struct.unpack('<I', block_data[24:28])[0]
        family_id = struct.unpack('<I', block_data[28:32])[0]
        payload_data = block_data[32:32+payload_size_bytes]

        return cls(block_data=block_data,
            flags=flags, 
            address=address, 
            payload_size_bytes=payload_size_bytes, 
            block_number=block_number, 
            total_blocks=total_blocks, 
            family_id=family_id, 
            payload_data=payload_data
        )

    @classmethod
    def from_contents(cls, flags, address, payload_size_bytes, block_number, total_blocks, family_id, payload_data):
        """
        Create a UF2 block from its contents.
        @param[in] flags 32-bit flags for UF2 block.
        @param[in] address Flash address to write payload_data to.
        @param[in] payload_size_bytes Number of Bytes of data within the payload (up to 476 Bytes).
        @param[in] block_number UF2 block number (out of total number of blocks).
        @param[in] total_blocks Total number of UF2 blocks in the file.
        @param[in] family_id ID of board to flash to.
        @param[in] payload_data Raw bytearray of size payload_size_bytes to be put into block_data and padded with zeros.
        """

        block_data = bytearray(cls.UF2_BLOCK_SIZE_BYTES)

        struct.pack_into('<I', block_data, 0, cls.UF2_MAGIC_START0)
        struct.pack_into('<I', block_data, 4, cls.UF2_MAGIC_START1)
        struct.pack_into('<I', block_data, 8, flags)  # flags
        struct.pack_into('<I', block_data, 12, address)  # address for CRC
        struct.pack_into('<I', block_data, 16, payload_size_bytes)  # payload size (4 bytes for CRC32)
        struct.pack_into('<I', block_data, 20, block_number)  # block number
        struct.pack_into('<I', block_data, 24, total_blocks)  # total blocks
        struct.pack_into('<I', block_data, 28, family_id)  # file size/family ID

        block_data[cls.UF2_HEADER_SIZE_BYTES:cls.UF2_HEADER_SIZE_BYTES+payload_size_bytes] = \
            payload_data[0:payload_size_bytes]
        block_data[cls.UF2_HEADER_SIZE_BYTES+payload_size_bytes:cls.UF2_BLOCK_SIZE_BYTES-cls.UF2_TAIL_SIZE_BYTES] = \
            [0 for i in range(cls.UF2_PAYLOAD_MAX_SIZE_BYTES - payload_size_bytes)]

        struct.pack_into('<I', block_data, cls.UF2_BLOCK_SIZE_BYTES - cls.UF2_TAIL_SIZE_BYTES, cls.UF2_MAGIC_END)

        return cls(block_data=block_data,
            flags=flags, 
            address=address, 
            payload_size_bytes=payload_size_bytes, 
            block_number=block_number, 
            total_blocks=total_blocks, 
            family_id=family_id, 
            payload_data=payload_data
        )

    def __str__(self):
        print_str = f"===UF2 BLOCK===\r\n"
        # Zero-index block numbers.
        print_str += f"flags: 0x{self.flags:x}\r\nblock number: {self.block_number}/{self.total_blocks-1}\r\n"
        print_str += f"address: 0x{self.address:x}\r\npayload size: {self.payload_size_bytes} Bytes\r\n"
        print_str += f"family id: 0x{self.family_id:x}\r\n"
        print_str += f"===============\r\n"
        return print_str

def uf2_file_to_blocks(filename):
    """
    Ingests a .uf2 file and returns a list of UF2Block objects.
    """
    with open(filename, 'rb') as f:
        uf2_data = f.read()
    
    num_blocks = len(uf2_data) // UF2Block.UF2_BLOCK_SIZE_BYTES
    print(f"Reading {filename}: {num_blocks} blocks\r\n")

    uf2_blocks = []
    for i in range(num_blocks):
        block_start = i*UF2Block.UF2_BLOCK_SIZE_BYTES
        uf2_blocks.append(UF2Block.from_block(uf2_data[block_start:block_start+UF2Block.UF2_BLOCK_SIZE_BYTES]))
    
    return uf2_blocks

def bin_file_to_uf2_file(bin_filename,
                         uf2_filename,
                         flags=0x2000,
                         start_address=0x10000000,
                         family_id=0xe48bff56,
                         payload_bytes_per_block=256):
    """
    Converts a .bin file to .uf2 format.
    """

    with open(bin_filename, 'rb') as f:
        bin_data = f.read()
    
    bin_size_bytes = len(bin_data)
    num_uf2_blocks = math.ceil(bin_size_bytes / payload_bytes_per_block)
    uf2_blocks:List[UF2Block] = []
    for i in range(num_uf2_blocks):
        bytes_remaining = bin_size_bytes - i*payload_bytes_per_block
        payload_size_bytes = min(bytes_remaining, payload_bytes_per_block)
        block_start_offset = i*payload_bytes_per_block
        
        uf2_blocks.append(UF2Block.from_contents(
            flags=flags,
            address=start_address+i*payload_bytes_per_block,
            payload_size_bytes=payload_size_bytes,
            block_number=i,
            total_blocks=num_uf2_blocks,
            family_id=family_id,
            payload_data=bin_data[block_start_offset:block_start_offset+payload_size_bytes]
        ))

    with open(uf2_filename, 'wb') as f:
        for block in uf2_blocks:
            f.write(block.block_data)

def dump_uf2_file(filename):
    uf2_blocks = uf2_file_to_blocks(filename)
    for block in uf2_blocks:
        print(block)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="UF2 Tools")
    parser.add_argument("filename_in")
    parser.add_argument("-d", "--dump", help="Dump contents of .uf2 file.", action="store_true")

    args = parser.parse_args()

    
    print("File:", args.filename_in)
    if args.dump:
        print("Dumping file contents.")
        dump_uf2_file(args.filename_in)