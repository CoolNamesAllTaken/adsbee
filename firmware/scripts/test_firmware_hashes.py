#!/usr/bin/env python3
"""Tests for firmware_hashes.py on small made-up images. Run: python3 firmware/scripts/test_firmware_hashes.py"""
import os
import struct
import sys
import tempfile
import unittest
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import firmware_hashes as fh  # noqa: E402


def uf2_block(addr, data):
    block = struct.pack("<8I", 0x0A324655, 0x9E5D5157, 0x2000, addr, len(data), 0, 1, 0xE48BFF56) + data
    return block.ljust(508, b"\0") + struct.pack("<I", 0x0AB16F30)


def hex_record(addr, record_type, data):
    raw = bytes([len(data), addr >> 8, addr & 0xFF, record_type]) + data
    return ":" + (raw + bytes([-sum(raw) & 0xFF])).hex().upper() + "\n"


class FirmwareHashesTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)

    def write(self, name, contents):
        path = os.path.join(self.dir.name, name)
        with open(path, "wb") as f:
            f.write(contents)
        return path

    def test_combine_is_crc32_of_little_endian_words(self):
        self.assertEqual(fh.combine([0x11111111, 0x22222222]), zlib.crc32(b"\x11" * 4 + b"\x22" * 4))

    def test_uf2_image_is_application_0_in_whole_blocks(self):
        app = [bytes([i]) * 256 for i in (1, 2)]
        uf2 = uf2_block(0x10000000, b"\xaa" * 256)  # Bootloader.
        uf2 += uf2_block(0x1002C000, b"\xbb" * 256)  # Partition header.
        uf2 += uf2_block(0x1002D000, app[0]) + uf2_block(0x1002D100, app[1])
        self.assertEqual(fh.uf2_rp2040_image(self.write("a.uf2", uf2)), app[0] + app[1])

    def test_ota_images_by_partition(self):
        images = [b"zero" * 10, b"one" * 7]
        parts = [struct.pack("<5I", 0xAD5BEEE, 0, len(i), zlib.crc32(i), 0xFFFFFFFF) + i for i in images]
        ota = struct.pack("<3I", 2, 12, 12 + len(parts[0])) + parts[0] + parts[1]
        self.assertEqual(fh.ota_rp2040_images(self.write("a.ota", ota)), images)
        with self.assertRaises(ValueError):
            fh.ota_rp2040_images(self.write("bad.ota", ota[:-1] + b"!"))

    def test_esp32_hash_is_start_of_elf_sha256(self):
        image = bytearray(512)
        image[0] = 0xE9
        struct.pack_into("<I", image, 32, 0xABCD5432)
        image[32 + 144 : 32 + 148] = bytes.fromhex("62127dbe")
        self.assertEqual(fh.esp32_hash(self.write("esp.bin", image)), 0x62127DBE)
        image[0] = 0
        with self.assertRaises(ValueError):
            fh.esp32_hash(self.write("bad.bin", image))

    def test_1421_hex_gaps_read_as_erased_flash(self):
        ccfg = bytes(range(fh.CC1314_CCFG_LEN))
        text = hex_record(0, 0, b"\x01\x02\x03\x04")
        text += hex_record(0, 2, struct.pack(">H", 0x1000)) + hex_record(2, 0, b"\x05\x06")  # 0x10002.
        text += hex_record(0, 4, struct.pack(">H", 0x5000)) + hex_record(0, 0, ccfg) + hex_record(0, 1, b"")
        path = self.write("a.hex", text.encode())

        class Args:
            hex = path

        image = b"\x01\x02\x03\x04" + b"\xff" * (0x10002 - 4) + b"\x05\x06"
        self.assertEqual(
            fh.hashes_1421(Args),
            [
                "CCFG_CC1314=0x{:08X}".format(zlib.crc32(ccfg)),
                "FIRMWARE=0x{:08X}".format(zlib.crc32(struct.pack("<I", zlib.crc32(image)))),
                "FIRMWARE_CC1314=0x{:08X} ({} Bytes)".format(zlib.crc32(image), len(image)),
            ],
        )


if __name__ == "__main__":
    unittest.main()
