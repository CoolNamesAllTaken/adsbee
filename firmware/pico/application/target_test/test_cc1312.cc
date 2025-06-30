#include "adsbee.hh"
#include "crc.hh"
#include "hardware_unit_tests.hh"
#include "unit_conversions.hh"

// Enable this define to run tests that muck with CC1312 settings and SRAM. This is only for use during development!
#define RUN_DISRUPTIVE_TESTS

#define NO_CC1312_EXIT_GUARD                                                      \
    if (!bsp.has_subg) {                                                          \
        CONSOLE_ERROR("CC1312", "No sub-GHz receiver installed. Skipping test."); \
        return;                                                                   \
    } else if (!adsbee.subg_radio.IsEnabled()) {                                  \
        CONSOLE_ERROR("CC1312", "CC1312 not enabled. Skipping test.");            \
        return;                                                                   \
    }

UTEST(CC1312, EnterBootloader) {
    NO_CC1312_EXIT_GUARD
    EXPECT_TRUE(adsbee.subg_radio_ll.EnterBootloader());
}

UTEST(CC1312, BootloaderCommandReset) {
    NO_CC1312_EXIT_GUARD
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandPing());
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandReset());
    EXPECT_FALSE(adsbee.subg_radio_ll.BootloaderCommandPing());
    sleep_ms(100);
    EXPECT_TRUE(adsbee.subg_radio_ll.EnterBootloader());
}

UTEST(CC1312, BootloaderCommandMemoryReadSingleWord) {
    NO_CC1312_EXIT_GUARD
    uint32_t read_buf_32[1] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + CC1312::kFCFG1RegOffUserID,
                                                                 read_buf_32, 1));
    printf("User ID (32 bit read): 0x%08X\n", read_buf_32[0]);
    uint8_t read_buf_8[4] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + CC1312::kFCFG1RegOffUserID,
                                                                 read_buf_8, 4));
    printf("User ID (8 bit read): 0x%02X%02X%02X%02X\n", read_buf_8[3], read_buf_8[2], read_buf_8[1], read_buf_8[0]);
    EXPECT_EQ(read_buf_32[0], read_buf_8[3] << 24 | read_buf_8[2] << 16 | read_buf_8[1] << 8 | read_buf_8[0]);
}

UTEST(CC1312, BootloaderCommandMemoryReadMultipleWords) {
    NO_CC1312_EXIT_GUARD
    // Read the following 3-word reset values sequence from the following registers in FCFG1.
    // Datasheet Table 11-25
    // 0x170 FLASH_E_P: 0x4C644C64
    // 0x174 FLASH_C_E_P_R: 0x0A0A2000
    // 0x178 FLASH_P_R_PV: 0x02C10200
    uint32_t read_buf_32[3] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x170, read_buf_32, 3));
    printf("FLASH_E_P: 0x%08X\n", read_buf_32[0]);
    printf("FLASH_C_E_P_R: 0x%08X\n", read_buf_32[1]);
    printf("FLASH_P_R_PV: 0x%08X\n", read_buf_32[2]);
    // Commented out these tests since it seems like the reset values from the datasheet don't match the actual values.
    // EXPECT_EQ(read_buf_32[0], 0x4C644C64);
    // EXPECT_EQ(read_buf_32[1], 0x0A0A2000);
    // EXPECT_EQ(read_buf_32[2], 0x02C10200);
    uint8_t read_buf_8[12] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x170, read_buf_8, 12));
    printf("FLASH_E_P: 0x%02X%02X%02X%02X\n", read_buf_8[3], read_buf_8[2], read_buf_8[1], read_buf_8[0]);
    printf("FLASH_C_E_P_R: 0x%02X%02X%02X%02X\n", read_buf_8[7], read_buf_8[6], read_buf_8[5], read_buf_8[4]);
    printf("FLASH_P_R_PV: 0x%02X%02X%02X%02X\n", read_buf_8[11], read_buf_8[10], read_buf_8[9], read_buf_8[8]);
    EXPECT_EQ(read_buf_32[0], read_buf_8[3] << 24 | read_buf_8[2] << 16 | read_buf_8[1] << 8 | read_buf_8[0]);
    EXPECT_EQ(read_buf_32[1], read_buf_8[7] << 24 | read_buf_8[6] << 16 | read_buf_8[5] << 8 | read_buf_8[4]);
    EXPECT_EQ(read_buf_32[2], read_buf_8[11] << 24 | read_buf_8[10] << 16 | read_buf_8[9] << 8 | read_buf_8[8]);
}

UTEST(CC1312, BootloaderCommandMemoryReadSingleWordMatchResetValue) {
    NO_CC1312_EXIT_GUARD
    uint32_t flash_otp_data4_reg = 0x0;
    EXPECT_TRUE(
        adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308, &flash_otp_data4_reg, 1));
    printf("FLASH_OTP_DATA4: 0x%08X\n", flash_otp_data4_reg);
    EXPECT_EQ(flash_otp_data4_reg, 0x98989F9F);  // Reset value from datasheet.
}

UTEST(CC1312, BootloaderCommandMemoryReadUnaligned) {
    NO_CC1312_EXIT_GUARD
    uint8_t read_buf;
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308 + 0, &read_buf, 1));
    EXPECT_EQ(read_buf, 0x9F);
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308 + 1, &read_buf, 1));
    EXPECT_EQ(read_buf, 0x9F);
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308 + 2, &read_buf, 1));
    EXPECT_EQ(read_buf, 0x98);
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308 + 3, &read_buf, 1));
    EXPECT_EQ(read_buf, 0x98);
}

#ifdef RUN_DISRUPTIVE_TESTS
UTEST(CC1312, BootloaderCommandMemoryWriteSingleWord) {
    NO_CC1312_EXIT_GUARD
    // Read and write with 32-bit word.
    uint32_t program_address =
        CC1312::kBaseAddrSRAM + 5e3;  // Arbitrary address in SRAM outside of lower 4kB (80kB total).
    uint32_t write_val = 0xDEADBEEF;
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryWrite(program_address, &write_val, 1));

    uint32_t read_val = 0x0;
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(program_address, &read_val, 1));
    printf("SRAM Test Word: 0x%08X\n", read_val);
    EXPECT_EQ(read_val, write_val);

    // Read and write with 8-bit buffer.
    uint8_t write_buf[4] = {0xFE, 0xED, 0xBE, 0xEF};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryWrite(program_address, write_buf, 4));
    uint8_t read_buf[4] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(program_address, read_buf, 4));
    printf("SRAM Test Word: 0x%02X%02X%02X%02X\n", read_buf[3], read_buf[2], read_buf[1], read_buf[0]);
    EXPECT_EQ(read_buf[0], 0xFE);
    EXPECT_EQ(read_buf[1], 0xED);
    EXPECT_EQ(read_buf[2], 0xBE);
    EXPECT_EQ(read_buf[3], 0xEF);

    // Read 8-bit buffer value back as 32-bit word.
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(program_address, &read_val, 1));
    EXPECT_EQ(read_val, 0xEFBEEDFE);
}

UTEST(CC1312, BootloaderCommandMemoryWriteMultipleWords) {
    NO_CC1312_EXIT_GUARD
    // Read and write with 32-bit word.
    uint32_t program_address =
        CC1312::kBaseAddrSRAM + 5e3;  // Arbitrary address in SRAM outside of lower 4kB (80kB total).
    uint32_t write_buf[3] = {0xDEADBEEF, 0xCAFEBABE, 0xFEEDFACE};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryWrite(program_address, write_buf, 3));

    uint32_t read_buf[3] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(program_address, read_buf, 3));
    EXPECT_EQ(read_buf[0], write_buf[0]);
    EXPECT_EQ(read_buf[1], write_buf[1]);
    EXPECT_EQ(read_buf[2], write_buf[2]);

    // Read and write with 8-bit buffer.
    uint8_t write_buf_8[12] = {0xFE, 0xED, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE, 0xFE, 0xED, 0xFA, 0xCE};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryWrite(program_address, write_buf_8, 12));
    uint8_t read_buf_8[12] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(program_address, read_buf_8, 12));
    printf("SRAM Test Words: 0x%02X%02X%02X%02X 0x%02X%02X%02X%02X 0x%02X%02X%02X%02X\n", read_buf_8[3], read_buf_8[2],
           read_buf_8[1], read_buf_8[0], read_buf_8[7], read_buf_8[6], read_buf_8[5], read_buf_8[4], read_buf_8[11],
           read_buf_8[10], read_buf_8[9], read_buf_8[8]);
    for (uint8_t i = 0; i < 12; i++) {
        EXPECT_EQ(read_buf_8[i], write_buf_8[i]);
    }
}
#endif  // RUN_DISRUPTIVE_TESTS

UTEST(CC1312, BootloaderReadCCFGConfig) {
    NO_CC1312_EXIT_GUARD
    CC1312::BootloaderCCFGConfig ccfg_config = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderReadCCFGConfig(ccfg_config));
    printf("CCFG Config:\n");
    printf("  Bank erase disabled: %s\n", ccfg_config.bank_erase_disabled ? "true" : "false");
    printf("  Chip erase disabled: %s\n", ccfg_config.chip_erase_disabled ? "true" : "false");
    printf("  Bootloader backdoor enabled: %s\n", ccfg_config.bl_backdoor_enabled ? "true" : "false");
    printf("  Bootloader backdoor pin: %d\n", ccfg_config.bl_backdoor_pin);
    printf("  Bootloader backdoor level: %s\n", ccfg_config.bl_backdoor_level ? "high" : "low");
    printf("  Bootloader enabled: %s\n", ccfg_config.bl_enabled ? "true" : "false");
}

UTEST(CC1312, BootloaderCRC32SingleWord) {
    NO_CC1312_EXIT_GUARD
    uint8_t buf[4] = {0x0};
    // Read FLASH_OTP_DATA4 register to get the reset value, which is 0x98989F9F.
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + 0x308, buf, 4));
    uint32_t num_bytes_to_crc = 1;
    uint32_t table_crc = crc32_ieee_802_3(buf, num_bytes_to_crc);
    printf("FLASH_OTP_DATA4: 0x%02X%02X%02X%02X\n", buf[3], buf[2], buf[1], buf[0]);
    printf("Table-Based CRC32 of FLASH_OTP_DATA4: 0x%08X\n", table_crc);
    uint32_t device_crc = 0x0;
    EXPECT_TRUE(
        adsbee.subg_radio_ll.BootloaderCommandCRC32(device_crc, CC1312::kBaseAddrFCFG1 + 0x308, num_bytes_to_crc));
    printf("Device-Based CRC32 of FLASH_OTP_DATA4: 0x%08X\n", device_crc);
    EXPECT_EQ(table_crc, device_crc);
}

UTEST(CC1312, BootloaderCRC32MultipleWords) {
    NO_CC1312_EXIT_GUARD
    uint32_t read_address = CC1312::kBaseAddrFCFG1 + 0x170;  // FLASH_E_P register.
    uint32_t read_num_bytes = 56;
    uint8_t read_buf[read_num_bytes] = {0};
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandMemoryRead(read_address, read_buf, read_num_bytes));
    uint32_t table_crc = crc32_ieee_802_3(read_buf, read_num_bytes);
    uint32_t device_crc = 0x0;
    EXPECT_TRUE(adsbee.subg_radio_ll.BootloaderCommandCRC32(device_crc, read_address, read_num_bytes));
    EXPECT_EQ(table_crc, device_crc);
}