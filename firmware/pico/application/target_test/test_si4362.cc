#include "adsbee.hh"
#include "hardware_unit_tests.hh"
#include "unit_conversions.hh"

// NOTE: These tests need to be run after the Si4362 is already initialized.

UTEST(Si4362, ReadPartInfo) {
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

UTEST(Si4362, SetGetProperty) {
    uint8_t preamble_config[] = {0xDE, 0XAD, 0XBE, 0XEF};
    EXPECT_TRUE(adsbee.r978.SetProperty(Si4362::kGroupPreamble, 4, 0x05, preamble_config));
    uint8_t read_buf[4] = {0};
    EXPECT_TRUE(adsbee.r978.GetProperty(Si4362::kGroupPreamble, 4, 0x05, read_buf));
    EXPECT_EQ(memcmp(preamble_config, read_buf, sizeof(preamble_config)), 0);
}

UTEST(Si4362, GetDeviceState) {
    Si4362::DeviceState state = Si4362::DeviceState::kStateInvalid;
    uint8_t channel = UINT8_MAX;
    EXPECT_TRUE(adsbee.r978.GetDeviceState(state, channel));
    printf("Device state: %s\r\n", adsbee.r978.DeviceStateToString(state));
    printf("Channel: %d\r\n", channel);
}

/**
 * Helper function used for reversing bytes in Sync Word, which are transmitted Big Endian in Bytes but Little Endian in
 * bits (smallest bit transmitted first, biggest Byte transmitted first).
 */
uint8_t reverse_byte(uint8_t byte) {
    uint8_t reversed = 0;
    for (int i = 0; i < 8; i++) {
        reversed |= ((byte >> i) & 0x1) << (7 - i);
    }
    return reversed;
}

void print_binary(uint8_t byte) {
    for (int i = 7; i >= 0; i--) {
        printf("%d", (byte >> i) & 0x1);
    }
}

UTEST(Si4362, GetSyncWord) {
    uint8_t data[6] = {0};
    EXPECT_TRUE(adsbee.r978.GetProperty(Si4362::kGroupSync, sizeof(data), 0x00, data));
    printf("Sync Word Configuration\r\n");
    printf("\tRX_ERRORS=%u\r\n", (data[0] >> 4) & 0b111);
    uint8_t sync_word_length_bytes = (data[0] & 0b11) + 1;
    printf("\tLENGTH=%u\r\n", sync_word_length_bytes);
    printf("\tBITS=");
    uint8_t sync_word[sync_word_length_bytes] = {0};
    for (uint8_t i = 0; i < sync_word_length_bytes; i++) {
        sync_word[i] = reverse_byte(data[i + 1]);
        print_binary(sync_word[i]);
    }
    printf("\r\n");
    printf("\tSYNC_ERROR_ONLY_BEGIN=%u\r\n", (data[5] >> 7) & 0b1);
}

UTEST(Si4362, GetModemDataRate) {
    Si4362::ModemConfig modem_config;
    EXPECT_TRUE(adsbee.r978.GetModemConfig(modem_config));
    modem_config.print();
}