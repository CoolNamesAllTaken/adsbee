#!/usr/bin/env python3
"""Tests for util_crc.py. Needs GNU objcopy. Run: python3 firmware/adsbee_1090/pico/linker_scripts/test_util_crc.py"""
import os
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import util_crc  # noqa: E402

OBJCOPY = os.environ.get("OBJCOPY", "objcopy")
HDR_ADDR = 0x1002C000
APP_ADDR = 0x1002D000


@unittest.skipIf(shutil.which(OBJCOPY) is None, "needs " + OBJCOPY)
class PatchElfHeaderTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)

    def path(self, name):
        return os.path.join(self.dir.name, name)

    def make_elf(self, header, app):
        """ELF with a .hdr0 section at the partition 0 header and an application section after it."""
        with open(self.path("hdr.bin"), "wb") as f:
            f.write(header)
        with open(self.path("app.bin"), "wb") as f:
            f.write(app)
        elf = self.path("combined.elf")
        subprocess.run([OBJCOPY, "-I", "binary", "-O", "elf32-i386", "-B", "i386", "--rename-section", ".data=.hdr0",
                        "--change-section-address", ".data=0x{:x}".format(HDR_ADDR), "--add-section",
                        ".text=" + self.path("app.bin"), "--set-section-flags", ".text=alloc,load,contents,code",
                        "--change-section-address", ".text=0x{:x}".format(APP_ADDR), self.path("hdr.bin"), elf],
                       check=True)
        return elf

    def flat(self, elf):
        subprocess.run([OBJCOPY, "-O", "binary", elf, self.path("flat.bin")], check=True)
        with open(self.path("flat.bin"), "rb") as f:
            return f.read()

    def test_header_describes_the_elf_application(self):
        app = bytes(range(256)) * 3 + b"\x01\x02\x03"
        # Header generated for another build (app0.bin), marked valid.
        stale = util_crc.create_header_bin_contents(5000, 0x12345678, status_valid=True)
        elf = self.make_elf(stale, app)
        util_crc.patch_elf_header(elf, OBJCOPY, ".hdr0", APP_ADDR - HDR_ADDR)
        flat = self.flat(elf)
        magic, version, size, crc, status = struct.unpack_from("<5I", flat, 0)
        self.assertEqual((magic, version, size, crc, status), (0xAD5BEEE, 0, len(app), zlib.crc32(app), 0xFFADFFFF))
        self.assertEqual(flat[APP_ADDR - HDR_ADDR:], app)  # Application unchanged.

    def test_patch_is_idempotent(self):
        elf = self.make_elf(bytes(20), b"\xaa" * 300)
        first = util_crc.patch_elf_header(elf, OBJCOPY, ".hdr0", APP_ADDR - HDR_ADDR)
        self.assertEqual(util_crc.patch_elf_header(elf, OBJCOPY, ".hdr0", APP_ADDR - HDR_ADDR), first)


if __name__ == "__main__":
    unittest.main()
