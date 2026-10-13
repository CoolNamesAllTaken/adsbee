#!/usr/bin/env python3
"""Prints the firmware and CCFG hashes AT+CONFIG_HASH? reports for a device running the given images.

  firmware_hashes.py adsbee_1090 [--uf2 adsbee_1090-<version>.uf2] [--ota adsbee_1090-<version>.ota]
                                 --esp32 adsbee_esp.bin --cc1312 sub_ghz_radio.bin
  firmware_hashes.py adsbee_1421 --hex adsbee_1421-<version>.hex

An ADSBee 1090 runs one of three RP2040 images: the one in the .uf2, or the .ota image for flash partition 0 or 1.
"""
import argparse
import struct
import sys
import zlib

RP2040_APP0_ADDR = 0x1002D000  # Application 0, the partition a .uf2 fills.
RP2040_APP_LEN = 8096 * 1024
UF2_BLOCK_LEN = 512
UF2_MAGICS = (0x0A324655, 0x9E5D5157, 0x0AB16F30)

ESP32_IMAGE_MAGIC = 0xE9
ESP32_APP_DESC_OFFSET = 32
ESP32_APP_DESC_MAGIC = 0xABCD5432
ESP32_APP_DESC_HASH_OFFSET = 144  # esp_app_desc_t.app_elf_sha256

CC1312_CCFG_ADDR = 0x57FA8  # CCFG fields at the end of the last flash page.
CC1312_CCFG_LEN = 0x58

CC1314_CCFG_ADDR = 0x50000000
CC1314_CCFG_LEN = 0x7C


def crc32(data):
    return zlib.crc32(bytes(data)) & 0xFFFFFFFF


def combine(hashes):
    """ConfigHasher::Combine(): CRC32 of the hashes as little-endian words."""
    return crc32(b"".join(struct.pack("<I", h) for h in hashes))


def read(path):
    with open(path, "rb") as f:
        return f.read()


def uf2_rp2040_image(path):
    """Application 0 as a .uf2 writes it: whole 256 Byte blocks."""
    contents = read(path)
    if len(contents) == 0 or len(contents) % UF2_BLOCK_LEN:
        raise ValueError("{} is not a UF2 file".format(path))
    image = bytearray()
    for offset in range(0, len(contents), UF2_BLOCK_LEN):
        block = contents[offset : offset + UF2_BLOCK_LEN]
        magic0, magic1, _, addr, size = struct.unpack_from("<IIIII", block)
        if (magic0, magic1, struct.unpack_from("<I", block, 508)[0]) != UF2_MAGICS:
            raise ValueError("{}: bad UF2 block at offset {}".format(path, offset))
        if not RP2040_APP0_ADDR <= addr < RP2040_APP0_ADDR + RP2040_APP_LEN:
            continue  # Bootloader or partition header.
        start = addr - RP2040_APP0_ADDR
        if start + size > len(image):
            image.extend(b"\xff" * (start + size - len(image)))
        image[start : start + size] = block[32 : 32 + size]
    if not image:
        raise ValueError("{} has no application image".format(path))
    return image


def ota_rp2040_images(path):
    """Application images in a .ota file, by partition."""
    contents = read(path)
    num_partitions = struct.unpack_from("<I", contents)[0]
    images = []
    for i in range(num_partitions):
        offset = struct.unpack_from("<I", contents, 4 + 4 * i)[0]
        magic, _, size, crc, _ = struct.unpack_from("<5I", contents, offset)
        image = contents[offset + 20 : offset + 20 + size]
        if magic != 0xAD5BEEE or len(image) != size or crc32(image) != crc:
            raise ValueError("{}: partition {} header does not match its image".format(path, i))
        images.append(image)
    return images


def esp32_hash(path):
    """First 4 Bytes of the application's ELF SHA-256, which the ESP32 reports while running."""
    image = read(path)
    desc_magic = struct.unpack_from("<I", image, ESP32_APP_DESC_OFFSET)[0]
    if image[0] != ESP32_IMAGE_MAGIC or desc_magic != ESP32_APP_DESC_MAGIC:
        raise ValueError("{} is not an ESP32 application image".format(path))
    offset = ESP32_APP_DESC_OFFSET + ESP32_APP_DESC_HASH_OFFSET
    return struct.unpack_from(">I", image, offset)[0]


def parse_intel_hex(path):
    """Returns {address: byte}."""
    memory = {}
    base = 0
    with open(path) as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            raw = bytes.fromhex(line[1:])
            if line[0] != ":" or sum(raw) & 0xFF or raw[0] != len(raw) - 5:
                raise ValueError("{}:{}: bad record".format(path, line_num))
            addr, record_type, data = (raw[1] << 8) | raw[2], raw[3], raw[4:-1]
            if record_type == 0:
                for i, b in enumerate(data):
                    memory[base + addr + i] = b
            elif record_type == 2:
                base = ((data[0] << 8) | data[1]) << 4
            elif record_type == 4:
                base = ((data[0] << 8) | data[1]) << 16
    return memory


def hashes_1090(args):
    if not args.uf2 and not args.ota:
        sys.exit("Give --uf2, --ota or both.")
    images = []
    if args.uf2:
        images.append(("UF2 image, partition 0", uf2_rp2040_image(args.uf2)))
    if args.ota:
        for partition, image in enumerate(ota_rp2040_images(args.ota)):
            images.append(("OTA image, partition {}".format(partition), image))
    cc1312 = read(args.cc1312)
    if len(cc1312) < CC1312_CCFG_ADDR + CC1312_CCFG_LEN:
        sys.exit("{} does not reach the CCFG.".format(args.cc1312))
    cc1312_crc = crc32(cc1312)
    esp32 = esp32_hash(args.esp32)

    lines = [
        "CCFG_CC1312=0x{:08X}".format(crc32(cc1312[CC1312_CCFG_ADDR : CC1312_CCFG_ADDR + CC1312_CCFG_LEN])),
        "FIRMWARE_ESP32=0x{:08X}".format(esp32),
        "FIRMWARE_CC1312=0x{:08X}".format(cc1312_crc),
    ]
    for name, image in images:
        rp2040_crc = crc32(image)
        lines += [
            "",
            "FIRMWARE=0x{:08X}".format(combine([rp2040_crc, esp32, cc1312_crc])),
            "FIRMWARE_RP2040=0x{:08X} ({}, {} Bytes)".format(rp2040_crc, name, len(image)),
        ]
    return lines


def hashes_1421(args):
    memory = parse_intel_hex(args.hex)
    ccfg = [memory.get(CC1314_CCFG_ADDR + i) for i in range(CC1314_CCFG_LEN)]
    if None in ccfg:
        sys.exit("{} has no complete CCFG.".format(args.hex))
    # Main flash from address 0 to the end of the image; a flasher leaves gaps erased.
    image_len = max(addr for addr in memory if addr < CC1314_CCFG_ADDR) + 1
    image = bytes(memory.get(addr, 0xFF) for addr in range(image_len))
    firmware_crc = crc32(image)

    return [
        "CCFG_CC1314=0x{:08X}".format(crc32(ccfg)),
        "FIRMWARE=0x{:08X}".format(combine([firmware_crc])),
        "FIRMWARE_CC1314=0x{:08X} ({} Bytes)".format(firmware_crc, image_len),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    products = parser.add_subparsers(dest="product", required=True)
    p1090 = products.add_parser("adsbee_1090")
    p1090.add_argument("--uf2", help="adsbee_1090-<version>.uf2 (combined.uf2)")
    p1090.add_argument("--ota", help="adsbee_1090-<version>.ota")
    p1090.add_argument("--esp32", required=True, help="ESP32 application image (adsbee_esp.bin)")
    p1090.add_argument("--cc1312", required=True, help="CC1312 image (sub_ghz_radio.bin)")
    p1090.set_defaults(func=hashes_1090)
    p1421 = products.add_parser("adsbee_1421")
    p1421.add_argument("--hex", required=True, help="adsbee_1421-<version>.hex")
    p1421.set_defaults(func=hashes_1421)
    for product in (p1090, p1421):
        product.add_argument("-o", "--output", help="also write the hashes to this file")
    args = parser.parse_args()
    try:
        lines = args.func(args)
        if args.output:
            with open(args.output, "w") as f:
                f.write("\n".join(lines) + "\n")
    except (OSError, ValueError, struct.error) as e:
        sys.exit("Error: {}".format(e))
    print("\n".join(lines))


if __name__ == "__main__":
    main()
