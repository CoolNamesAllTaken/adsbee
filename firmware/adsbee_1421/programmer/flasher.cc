#include "flasher.hh"

#include "firmware_image.hh"
#include "status.hh"

static const uint32_t kCcfgBase = 0x50000000;

bool BakedImageMatches(Cc13x4Bootloader& bl) {
    for (unsigned i = 0; i < kFirmwareNumSegments; i++) {
        const FirmwareSegment& seg = kFirmwareSegments[i];
        uint32_t device_crc;
        if (!bl.Crc32(seg.addr, seg.len, &device_crc)) return false;
        if (device_crc != seg.crc32) {
            CdcPrintf("CRC mismatch @ 0x%08lX: device 0x%08lX, baked 0x%08lX\r\n",
                      (unsigned long)seg.addr, (unsigned long)device_crc,
                      (unsigned long)seg.crc32);
            return false;
        }
    }
    return true;
}

FlashResult FlashBakedImage(Cc13x4Bootloader& bl) {
    uint32_t chip_id;
    if (bl.GetChipId(&chip_id)) {
        CdcPrintf("Chip ID: 0x%08lX\r\n", (unsigned long)chip_id);
    }

    CdcPrintf("Erasing main flash bank...\r\n");
    if (!bl.BankErase()) return FlashResult::kEraseFailed;
    // Erasing CCFG restores TI factory defaults (bootloader enabled), so an interrupted flash
    // is always recoverable over UART. The CCFG segment is programmed last for the same reason.
    CdcPrintf("Erasing CCFG sector...\r\n");
    if (!bl.SectorErase(kCcfgBase)) return FlashResult::kEraseFailed;

    for (unsigned i = 0; i < kFirmwareNumSegments; i++) {
        const FirmwareSegment& seg = kFirmwareSegments[i];
        CdcPrintf("Programming 0x%08lX (%lu bytes)\r\n", (unsigned long)seg.addr,
                  (unsigned long)seg.len);
        if (!bl.Download(seg.addr, seg.len)) return FlashResult::kProgramFailed;
        uint32_t sent = 0;
        uint32_t next_report = 0;
        while (sent < seg.len) {
            uint32_t chunk = seg.len - sent;
            if (chunk > Cc13x4Bootloader::kMaxDataChunk) chunk = Cc13x4Bootloader::kMaxDataChunk;
            if (!bl.SendData(seg.data + sent, chunk)) return FlashResult::kProgramFailed;
            sent += chunk;
            if (sent >= next_report) {
                CdcPrintf("  %lu/%lu bytes (%lu%%)\r\n", (unsigned long)sent,
                          (unsigned long)seg.len, (unsigned long)(100 * sent / seg.len));
                next_report += 65536;
            }
        }
    }

    StatusSet(Status::kVerifying);
    CdcPrintf("Verifying...\r\n");
    if (!BakedImageMatches(bl)) return FlashResult::kVerifyFailed;
    CdcPrintf("CRC32 verified, flash complete.\r\n");
    return FlashResult::kOk;
}
