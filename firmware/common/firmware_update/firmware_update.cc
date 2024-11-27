#include "firmware_update.hh"

// Start addresses.
const uint32_t FirmwareUpdateManager::kFlashHeaderStartAddrs[] = {
    FirmwareUpdateManager::kFlashBlStartAddr + FirmwareUpdateManager::kFlashBlLenBytes,
    FirmwareUpdateManager::kFlashHeaderStartAddrs[0] + FirmwareUpdateManager::kFlashHeaderLenBytes +
        FirmwareUpdateManager::kFlashAppLenBytes};
const uint32_t FirmwareUpdateManager::kFlashAppStartAddrs[] = {
    FirmwareUpdateManager::kFlashHeaderStartAddrs[0] + FirmwareUpdateManager::kFlashHeaderLenBytes,
    FirmwareUpdateManager::kFlashHeaderStartAddrs[1] + FirmwareUpdateManager::kFlashHeaderLenBytes};

// Convenience arrays for accessing headers and apps.
const FirmwareUpdateManager::FlashPartitionHeader
    *FirmwareUpdateManager::flash_partition_headers[FirmwareUpdateManager::kNumPartitions] = {
        (FirmwareUpdateManager::FlashPartitionHeader *)FirmwareUpdateManager::kFlashHeaderStartAddrs[0],
        (FirmwareUpdateManager::FlashPartitionHeader *)FirmwareUpdateManager::kFlashHeaderStartAddrs[1]};
const uint8_t *FirmwareUpdateManager::flash_partition_apps[FirmwareUpdateManager::kNumPartitions] = {
    (uint8_t *)FirmwareUpdateManager::kFlashAppStartAddrs[0], (uint8_t *)FirmwareUpdateManager::kFlashAppStartAddrs[1]};

uint32_t FirmwareUpdateManager::stored_interrupts_ = 0;
