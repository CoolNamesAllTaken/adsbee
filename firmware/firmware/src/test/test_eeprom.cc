#include "eeprom.hh"
#include "hardware/i2c.h"
#include "hardware_unit_tests.hh"

static bool reserved_addr(uint8_t addr) { return (addr & 0x78) == 0 || (addr & 0x78) == 0x78; }

void i2c_bus_scan(i2c_inst_t *i2c_handle, uint32_t i2c_timeout_us) {
    // i2c_init(i2c_handle, 100 * 1000);
    // gpio_set_function(2, GPIO_FUNC_I2C);
    // gpio_set_function(3, GPIO_FUNC_I2C);
    // gpio_pull_up(2);
    // gpio_pull_up(3);

    DEBUG_PRINTF("\ni2c_write_blocking test\n");
    DEBUG_PRINTF("   0  1  2  3  4  5  6  7  8  9  A  B  C  D  E  F\n");

    for (int addr = 0; addr < (1 << 7); ++addr) {
        if (addr % 16 == 0) {
            DEBUG_PRINTF("%02x ", addr);
        }

        int ret;
        uint8_t rxdata = 0;
        if (reserved_addr(addr)) {
            ret = PICO_ERROR_GENERIC;
        } else {
            ret = i2c_read_timeout_us(i2c_handle, addr, &rxdata, 1, false, i2c_timeout_us);
            if (ret != 1) {
                DEBUG_PRINTF("i2c_bus_scan: Read failed at address 0x%x with code %d.\r\n", addr, ret);
            }
        }

        DEBUG_PRINTF(ret < 0 ? "." : "@");
        DEBUG_PRINTF(addr % 16 == 15 ? "\n" : "  ");
    }
}

UTEST(EEPROM, BasicWritReadByte) {
    ASSERT_GE(eeprom.WriteByte(0x0, 0xDE), 0);
    ASSERT_GE(eeprom.WriteByte(0x1, 0xAD), 0);
    ASSERT_GE(eeprom.WriteByte(0x2, 0xBE), 0);
    ASSERT_GE(eeprom.WriteByte(0x3, 0xEF), 0);
    uint8_t byte;
    ASSERT_GE(eeprom.ReadByte(0x0, byte), 0);
    ASSERT_EQ(byte, 0xDE);
    ASSERT_GE(eeprom.ReadByte(0x1, byte), 0);
    ASSERT_EQ(byte, 0xAD);
    ASSERT_GE(eeprom.ReadByte(0x2, byte), 0);
    ASSERT_EQ(byte, 0xBE);
    ASSERT_GE(eeprom.ReadByte(0x3, byte), 0);
    ASSERT_EQ(byte, 0xEF);
}