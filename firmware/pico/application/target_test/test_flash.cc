#include "firmware_update.hh"
#include "hardware_unit_tests.hh"

int16_t own_partition = -1;
int16_t other_partition = -1;

UTEST(Flash, AmWithinFlashPartition) {
    for (uint16_t i = 0; i < FirmwareUpdateManager::kNumPartitions; i++) {
        if (FirmwareUpdateManager::AmWithinFlashPartition(i)) {
            own_partition = i;
        } else {
            other_partition = i;
        }
    }
    ASSERT_GE_MSG(own_partition, 0, "Never found own partition.");
    ASSERT_GE_MSG(other_partition, 0, "Never found other partition.");
    ASSERT_NE_MSG(own_partition, other_partition, "Partitions can't match!");
}

UTEST(Flash, CRC32) {
    uint8_t sequence[] = {0xEF, 0xBE, 0xAD, 0xBE, 0xEF, 0xBE, 0xAD, 0xBE};
    uint32_t expected_crc = 0x3341B647;
    ASSERT_EQ(FirmwareUpdateManager::CalculateCRC32(sequence, sizeof(sequence)), expected_crc);
}

UTEST(Flash, VerifyOwnPartition) { ASSERT_TRUE(FirmwareUpdateManager::VerifyFlashPartition(own_partition)); }