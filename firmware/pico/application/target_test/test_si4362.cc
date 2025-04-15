#include "hardware_unit_tests.hh"
#include "adsbee.hh"

// NOTE: These tests need to be run after the Si4362 is already initialized.

UTEST(Si4362, WriteReadStuff) {
    EXPECT_TRUE(adsbee.r978.SendCommand(Si4362::Command::kCmdNop));
    uint8_t part_info_buf[8] = {0};
    EXPECT_TRUE(adsbee.r978.ReadCommand(Si4362::Command::kCmdPartInfo, part_info_buf, sizeof(part_info_buf)));
    printf("\tChip Revision: %d\r\n", part_info_buf[0]);
    printf("\tPart Number: 0x%X\r\n", (part_info_buf[1] << 8) | part_info_buf[2]);
    printf("\tPbuild: %d\r\n", part_info_buf[3]);
    printf("\tID: %d\r\n", (part_info_buf[4] << 8) | part_info_buf[5]);
    printf("\tCustomer: %d\r\n", part_info_buf[6]);
    printf("\tROM ID: %d\r\n", part_info_buf[7]);
}