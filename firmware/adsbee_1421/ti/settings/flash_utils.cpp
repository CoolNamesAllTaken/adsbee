#include "flash_utils.hh"

#include <ti/devices/cc13x4_cc26x4/driverlib/flash.h>
#include <ti/devices/cc13x4_cc26x4/driverlib/interrupt.h>

uint32_t FlashUtils::stored_key_ = 0;

void FlashUtils::FlashSafe() {
    stored_key_ = IntMasterDisable();
}

void FlashUtils::FlashUnsafe() {
    if (!stored_key_) {
        IntMasterEnable();
    }
}

void FlashUtils::EraseRegion(uint32_t addr) {
    for (uint32_t offset = 0; offset < kFlashSettingsRegionSizeBytes; offset += kFlashSectorSizeBytes) {
        FlashSectorErase(addr + offset);
    }
}

void FlashUtils::EraseSector(uint32_t addr) { FlashSectorErase(addr); }

void FlashUtils::Program(uint32_t addr, const uint8_t* data, uint32_t size) {
    FlashProgram(const_cast<uint8_t*>(data), addr, size);
}