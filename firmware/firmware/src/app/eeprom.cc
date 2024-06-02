#include "eeprom.hh"

#include <cstring>

#include "hal.hh"           // For timing.
#include "hardware/gpio.h"  // For optional I2C initialization.
#include "hardware/i2c.h"

void EEPROM::WaitForSafeWriteTime() {
    WaitForSafeReadTime();
    last_write_timestamp_us_ = get_time_since_boot_us();
}

void EEPROM::WaitForSafeReadTime() {
    while ((uint32_t)(get_time_since_boot_us() - last_write_timestamp_us_) < config_.i2c_write_time_us) {
        // Block until write has completed.
    }
}

int EEPROM::WriteByte(const uint8_t reg, const uint8_t byte) {
    uint8_t msg[2];
    msg[0] = reg;
    msg[1] = byte;
    WaitForSafeWriteTime();
    int ret = i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, 2, false, config_.i2c_timeout_us);
    if (ret < 0) DEBUG_PRINTF("EEPROM::WriteByte: Write to register 0x%d failed with code %d.\r\n", reg, ret);
    return ret;
}

int EEPROM::ReadByte(const uint8_t reg, uint8_t &byte) {
    // Write address to read from.
    WaitForSafeReadTime();
    int status = i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, &reg, 1, true, config_.i2c_timeout_us);
    if (status < 0) return status;
    // Read reply and put it into byte.
    return i2c_read_timeout_us(config_.i2c_handle, config_.i2c_addr, &byte, 1, false, config_.i2c_timeout_us);
}

int EEPROM::WriteBuf(const uint8_t reg, uint8_t *buf, const uint16_t num_bytes) {
    // Check to make sure caller is sending 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }
    // Check to make sure registers are in bounds.
    if (reg + num_bytes > config_.size_bytes) {
        DEBUG_PRINTF("EEPROM::WriteBuf: Write of %d bytes at 0x%x overruns end of EEPROM.\r\n");
        return PICO_ERROR_INVALID_ARG;
    }

    uint8_t write_reg = reg;
    while (write_reg < reg + num_bytes) {
        uint8_t num_bytes_written = write_reg - reg;
        uint8_t page_bytes_remaining = config_.page_size_bytes - (write_reg % config_.page_size_bytes);
        uint8_t write_num_bytes = MIN(page_bytes_remaining, num_bytes - num_bytes_written);
        uint8_t msg[write_num_bytes + 1];  // Add a spot for the address.
        msg[0] = write_reg;
        for (uint16_t i = 0; i < write_num_bytes; i++) {
            msg[i + 1] = buf[num_bytes_written + i];
        }
        WaitForSafeWriteTime();
        int status = i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, write_num_bytes + 1, false,
                                          config_.i2c_timeout_us);
        if (status < 0) {
            DEBUG_PRINTF("EEPROM::I2CRegWrite: Write failed at register 0x%x while trying to write %d bytes.\r\n",
                         write_reg, write_num_bytes);
            return status;
        }
        write_reg += write_num_bytes;
    }

    return num_bytes;
}

int EEPROM::ReadBuf(const uint8_t reg, uint8_t *buf, const uint16_t num_bytes) {
    int num_bytes_read = 0;

    // Check to make sure caller is asking for 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }
    // Check to make sure registers are in bounds.
    if (reg + num_bytes > config_.size_bytes) {
        DEBUG_PRINTF("EEPROM::ReadBuf: Read of %d bytes at 0x%x overruns end of EEPROM.\r\n");
        return PICO_ERROR_INVALID_ARG;
    }

    // Read data from register(s) over I2C
    WaitForSafeReadTime();
    i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, &reg, 1, true, config_.i2c_timeout_us);
    num_bytes_read =
        i2c_read_timeout_us(config_.i2c_handle, config_.i2c_addr, buf, num_bytes, false, config_.i2c_timeout_us);

    return num_bytes_read;
}

bool EEPROM::Init() {
    if (config_.requires_init) {
        // Initialize I2C for talking to the EEPROM and rx gain digipot.
        i2c_init(config_.i2c_handle, config_.onboard_i2c_clk_freq_hz);
        gpio_set_function(config_.onboard_i2c_sda_pin, GPIO_FUNC_I2C);
        gpio_set_function(config_.onboard_i2c_scl_pin, GPIO_FUNC_I2C);
    }

    uint8_t eeprom_random_address_data;
    if (i2c_read_timeout_us(config_.i2c_handle, config_.i2c_addr, &eeprom_random_address_data, 1, false,
                            config_.i2c_timeout_us) != 1) {
        DEBUG_PRINTF("EEPROM::Init: Failed to read current address from EEPROM at I2C address 0x%x.\r\n",
                     config_.i2c_addr);
        return false;
    }
    return true;
}

void EEPROM::Dump() {
    DEBUG_PRINTF("EEPROM::Dump:\r\n");
    // Print header row.
    DEBUG_PRINTF("\tPG ");
    for (uint16_t i = 0; i < config_.page_size_bytes; i++) {
        DEBUG_PRINTF("  %02x", i);
    }
    DEBUG_PRINTF("\r\n\r\n");
    // Print EEPROM contents.
    for (uint16_t page = 0; page < config_.size_bytes / config_.page_size_bytes; page++) {
        uint8_t page_start = page * config_.page_size_bytes;
        DEBUG_PRINTF("\t%02x:", page_start);
        for (uint16_t i = 0; i < config_.page_size_bytes; i++) {
            uint8_t byte_addr = page_start + i;
            uint8_t byte;
            int status = ReadByte(byte_addr, byte);
            if (status < 0) {
                DEBUG_PRINTF("  ??");  // Indicate read failure with question marks.
            }
            DEBUG_PRINTF("  %02x", byte);
        }
        DEBUG_PRINTF("\r\n");  // End of page.
    }
}