#include "flash_utils.hh"

#include <ti/devices/cc13x4_cc26x4/driverlib/flash.h>
#include <ti/devices/cc13x4_cc26x4/driverlib/interrupt.h>

#include "crc.hh"

extern "C" const uint8_t __flash_image_end__;  // Linker script symbol.

uint32_t FlashUtils::stored_key_ = 0;

void FlashUtils::FlashSafe() {
    stored_key_ = IntMasterDisable();
}

void FlashUtils::FlashUnsafe() {
    if (!stored_key_) {
        IntMasterEnable();
    }
}

// The driverlib flash calls return FAPI_STATUS_SUCCESS or an error code. Callers persist settings with
// these, so a silently dropped error is how a half-written blob ends up in flash — always propagate.

bool FlashUtils::EraseRegion(uint32_t addr) {
    for (uint32_t offset = 0; offset < kFlashSettingsRegionSizeBytes; offset += kFlashSectorSizeBytes) {
        if (!EraseSector(addr + offset)) {
            return false;  // Bail out rather than program into a region that is only partly erased.
        }
    }
    return true;
}

bool FlashUtils::EraseSector(uint32_t addr) { return FlashSectorErase(addr) == FAPI_STATUS_SUCCESS; }

bool FlashUtils::Program(uint32_t addr, const uint8_t* data, uint32_t size) {
    return FlashProgram(const_cast<uint8_t*>(data), addr, size) == FAPI_STATUS_SUCCESS;
}

uint32_t FlashUtils::ImageCRC32(uint32_t& len_bytes) {
    len_bytes = reinterpret_cast<uint32_t>(&__flash_image_end__);
    // Volatile so the compiler can't treat flash address 0 as a null pointer.
    const uint8_t* volatile image = reinterpret_cast<const uint8_t*>(0);
    return crc32_ieee_802_3(image, len_bytes);
}
