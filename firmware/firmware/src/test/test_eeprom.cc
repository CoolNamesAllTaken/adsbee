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

    CONSOLE_PRINTF("\ni2c_write_blocking test\n");
    CONSOLE_PRINTF("   0  1  2  3  4  5  6  7  8  9  A  B  C  D  E  F\n");

    for (int addr = 0; addr < (1 << 7); ++addr) {
        if (addr % 16 == 0) {
            CONSOLE_PRINTF("%02x ", addr);
        }

        int ret;
        uint8_t rxdata = 0;
        if (reserved_addr(addr)) {
            ret = PICO_ERROR_GENERIC;
        } else {
            ret = i2c_read_timeout_us(i2c_handle, addr, &rxdata, 1, false, i2c_timeout_us);
            if (ret != 1) {
                CONSOLE_PRINTF("i2c_bus_scan: Read failed at address 0x%x with code %d.\r\n", addr, ret);
            }
        }

        CONSOLE_PRINTF(ret < 0 ? "." : "@");
        CONSOLE_PRINTF(addr % 16 == 15 ? "\n" : "  ");
    }
}

UTEST(EEPROM, BasicWriteReadByte) {
    ASSERT_GE(eeprom.WriteByte(0x0, 0x00), 0);
    ASSERT_GE(eeprom.WriteByte(0x1, 0x11), 0);
    ASSERT_GE(eeprom.WriteByte(0x2, 0x22), 0);
    ASSERT_GE(eeprom.WriteByte(0x3, 0x33), 0);
    ASSERT_GE(eeprom.WriteByte(0x4, 0x44), 0);
    ASSERT_GE(eeprom.WriteByte(0x5, 0x55), 0);
    ASSERT_GE(eeprom.WriteByte(0x6, 0x66), 0);
    ASSERT_GE(eeprom.WriteByte(0x7, 0x77), 0);
    ASSERT_GE(eeprom.WriteByte(0x8, 0x88), 0);
    ASSERT_GE(eeprom.WriteByte(0x9, 0x99), 0);
    ASSERT_GE(eeprom.WriteByte(0xA, 0xAA), 0);
    ASSERT_GE(eeprom.WriteByte(0xB, 0xBB), 0);
    ASSERT_GE(eeprom.WriteByte(0xC, 0xCC), 0);
    ASSERT_GE(eeprom.WriteByte(0xD, 0xDD), 0);
    ASSERT_GE(eeprom.WriteByte(0xE, 0xEE), 0);
    ASSERT_GE(eeprom.WriteByte(0xF, 0xFF), 0);
    uint8_t byte;
    ASSERT_GE(eeprom.ReadByte(0x0, byte), 0);
    EXPECT_EQ(byte, 0x00);
    ASSERT_GE(eeprom.ReadByte(0x1, byte), 0);
    EXPECT_EQ(byte, 0x11);
    ASSERT_GE(eeprom.ReadByte(0x2, byte), 0);
    EXPECT_EQ(byte, 0x22);
    ASSERT_GE(eeprom.ReadByte(0x3, byte), 0);
    EXPECT_EQ(byte, 0x33);
    ASSERT_GE(eeprom.ReadByte(0x4, byte), 0);
    EXPECT_EQ(byte, 0x44);
    ASSERT_GE(eeprom.ReadByte(0x5, byte), 0);
    EXPECT_EQ(byte, 0x55);
    ASSERT_GE(eeprom.ReadByte(0x6, byte), 0);
    EXPECT_EQ(byte, 0x66);
    ASSERT_GE(eeprom.ReadByte(0x7, byte), 0);
    EXPECT_EQ(byte, 0x77);
    ASSERT_GE(eeprom.ReadByte(0x8, byte), 0);
    EXPECT_EQ(byte, 0x88);
    ASSERT_GE(eeprom.ReadByte(0x9, byte), 0);
    EXPECT_EQ(byte, 0x99);
    ASSERT_GE(eeprom.ReadByte(0xA, byte), 0);
    EXPECT_EQ(byte, 0xAA);
    ASSERT_GE(eeprom.ReadByte(0xB, byte), 0);
    EXPECT_EQ(byte, 0xBB);
    ASSERT_GE(eeprom.ReadByte(0xC, byte), 0);
    EXPECT_EQ(byte, 0xCC);
    ASSERT_GE(eeprom.ReadByte(0xD, byte), 0);
    EXPECT_EQ(byte, 0xDD);
    ASSERT_GE(eeprom.ReadByte(0xE, byte), 0);
    EXPECT_EQ(byte, 0xEE);
    ASSERT_GE(eeprom.ReadByte(0xF, byte), 0);
    EXPECT_EQ(byte, 0xFF);
}

UTEST(EEPROM, WriteReadBuf) {
    uint8_t reg_addr = 0x1A;  // Write across a page boundary.
    uint8_t buf[] = {0xDE, 0xAD, 0xBE, 0xEF, 0xBE, 0xEE, 0xEE, 0xEF, 0xAA,
                     0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00, 0x11, 0x22};
    uint16_t buf_size = sizeof(buf);
    ASSERT_GE(eeprom.WriteBuf(reg_addr, buf, buf_size), 0);
    uint8_t byte;
    for (uint16_t i = 0; i < buf_size; i++) {
        ASSERT_GE(eeprom.ReadByte(reg_addr + i, byte), 0);
        EXPECT_EQ(byte, buf[i]);
    }
    eeprom.Dump();

    uint8_t buf_out[buf_size];
    ASSERT_GE(eeprom.ReadBuf(reg_addr, buf_out, buf_size), 0);
    for (uint16_t i = 0; i < buf_size; i++) {
        EXPECT_EQ(buf[i], buf_out[i]);
    }
}

UTEST(EEPROM, LoadSaveObject) {
    struct TestObject {
        char message[200];
        uint32_t value;
    };

    TestObject object_in = {.message = "Hello its a me a test object Mario.", .value = 0xFEFEDEDA};
    TestObject object_out;

    // Nominal save and load.
    ASSERT_TRUE(eeprom.Save(object_in));
    ASSERT_TRUE(eeprom.Load(object_out));
    ASSERT_STREQ(object_in.message, object_out.message);
    ASSERT_EQ(object_in.value, object_out.value);

    // Clear object out.
    object_out.message[0] = '\0';
    object_out.value = 0x0;

    // Custom address save and load.
    ASSERT_TRUE(eeprom.Save(object_in, 0x20));
    ASSERT_TRUE(eeprom.Load(object_out, 0x20));

    // Out of bounds save and load should fail.
    ASSERT_FALSE(eeprom.Save(object_in, 0xc0));
    ASSERT_FALSE(eeprom.Load(object_in, 0xc0));
}