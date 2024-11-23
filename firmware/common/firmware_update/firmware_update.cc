#include "firmware_update.hh"

// Initialize static const arrays.
const uint32_t FirmwareUpdateManager::kFlashHeaderStartAddrs[] = {
    FirmwareUpdateManager::kFlashBlStartAddr + FirmwareUpdateManager::kFlashBlLenBytes,
    FirmwareUpdateManager::kFlashHeaderStartAddrs[0] + FirmwareUpdateManager::kFlashHeaderLenBytes +
        FirmwareUpdateManager::kFlashAppLenBytes};
const uint32_t FirmwareUpdateManager::kFlashAppStartAddrs[] = {
    FirmwareUpdateManager::kFlashHeaderStartAddrs[0] + FirmwareUpdateManager::kFlashHeaderLenBytes,
    FirmwareUpdateManager::kFlashHeaderStartAddrs[1] + FirmwareUpdateManager::kFlashHeaderLenBytes};

uint32_t FirmwareUpdateManager::stored_interrupts_ = 0;