#include "eeprom.hh"

#include <cstring>

#include "hal.hh"           // For timing.
#include "hardware/gpio.h"  // For optional I2C initialization.
#include "hardware/i2c.h"

void EEPROM::BeginPostWriteDelay() { last_write_timestamp_us_ = get_time_since_boot_us(); }

void EEPROM::WaitForSafeReadWriteTime() {
    while ((uint32_t)(get_time_since_boot_us() - last_write_timestamp_us_) < config_.i2c_write_time_us) {
        // Block until write has completed.
    }
}

int EEPROM::WriteByte(const uint16_t reg, const uint8_t byte) {
    uint8_t msg[kRegAddrNumBytes + 1];
    msg[0] = reg >> 8;
    msg[1] = reg & 0xFF;
    msg[2] = byte;
    WaitForSafeReadWriteTime();
    int ret =
        i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, sizeof(msg), false, config_.i2c_timeout_us);
    BeginPostWriteDelay();
    if (ret < 0) CONSOLE_ERROR("EEPROM::WriteByte: Write to register 0x%d failed with code %d.", reg, ret);
    return ret;
}

int EEPROM::ReadByte(const uint16_t reg, uint8_t &byte) {
    // Write address to read from.
    uint8_t msg[kRegAddrNumBytes];
    msg[0] = reg >> 8;
    msg[1] = reg & 0xFF;
    WaitForSafeReadWriteTime();
    int status =
        i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, sizeof(msg), true, config_.i2c_timeout_us);
    if (status < 0) return status;
    // Read reply and put it into byte.
    return i2c_read_timeout_us(config_.i2c_handle, config_.i2c_addr, &byte, 1, false, config_.i2c_timeout_us);
}

int EEPROM::WriteBuf(const uint16_t reg, uint8_t *buf, const uint16_t num_bytes) {
    // Check to make sure caller is sending 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }
    // Check to make sure registers are in bounds.
    if (reg + num_bytes > config_.size_bytes) {
        CONSOLE_ERROR("EEPROM::WriteBuf: Write of %d bytes at 0x%x overruns end of EEPROM.", num_bytes, reg);
        return PICO_ERROR_INVALID_ARG;
    }

    uint16_t write_reg = reg;
    while (write_reg < reg + num_bytes) {
        uint16_t num_bytes_written = write_reg - reg;
        uint16_t page_bytes_remaining = config_.page_size_bytes - (write_reg % config_.page_size_bytes);
        uint16_t write_num_bytes = MIN(page_bytes_remaining, num_bytes - num_bytes_written);
        uint8_t msg[write_num_bytes + kRegAddrNumBytes];  // Add a spot for the address.
        msg[0] = write_reg >> 8;
        msg[1] = write_reg & 0xFF;
        for (uint16_t i = 0; i < write_num_bytes; i++) {
            msg[i + kRegAddrNumBytes] = buf[num_bytes_written + i];
        }
        WaitForSafeReadWriteTime();
        int status =
            i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, sizeof(msg), false, config_.i2c_timeout_us);
        BeginPostWriteDelay();
        if (status < 0) {
            CONSOLE_ERROR(
                "EEPROM::I2CRegWrite: Write failed at register 0x%x while trying to write %d bytes, with error code "
                "%d.",
                write_reg, write_num_bytes, status);
            return status;
        }
        if (status != kRegAddrNumBytes + write_num_bytes) {
            CONSOLE_ERROR(
                "EEPROM::I2CRegWrite: Write failed at register 0x%x, expected to write %d bytes including register "
                "address but wrote %d.",
                write_reg, write_num_bytes, status);
            return INT32_MIN;
        }
        write_reg += write_num_bytes;
    }

    return num_bytes;
}

int EEPROM::ReadBuf(const uint16_t reg, uint8_t *buf, const uint16_t num_bytes) {
    int num_bytes_read = 0;

    // Check to make sure caller is asking for 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }
    // Check to make sure registers are in bounds.
    if (reg + num_bytes > config_.size_bytes) {
        CONSOLE_ERROR("EEPROM::ReadBuf: Read of %d bytes at 0x%x overruns end of EEPROM.", num_bytes, reg);
        return PICO_ERROR_INVALID_ARG;
    }

    // Read data from register(s) over I2C
    uint8_t msg[kRegAddrNumBytes];
    msg[0] = reg >> 8;
    msg[1] = reg & 0xFF;
    WaitForSafeReadWriteTime();
    i2c_write_timeout_us(config_.i2c_handle, config_.i2c_addr, msg, sizeof(msg), true, config_.i2c_timeout_us);
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
        CONSOLE_ERROR("EEPROM::Init: Failed to read current address from EEPROM at I2C address 0x%x.",
                      config_.i2c_addr);
        return false;
    }
    return true;
}

void EEPROM::Dump() {
    CONSOLE_PRINTF("EEPROM::Dump:\r\n");
    // Print header row.
    CONSOLE_PRINTF("\tPG ");
    for (uint16_t i = 0; i < config_.page_size_bytes; i++) {
        CONSOLE_PRINTF("  %02x", i);
    }
    CONSOLE_PRINTF("\r\n\r\n");
    // Print EEPROM contents.
    for (uint16_t page = 0; page < config_.size_bytes / config_.page_size_bytes; page++) {
        uint16_t page_start = page * config_.page_size_bytes;
        CONSOLE_PRINTF("\t%02x:", page_start);
        for (uint16_t i = 0; i < config_.page_size_bytes; i++) {
            uint16_t byte_addr = page_start + i;
            uint8_t byte;
            int status = ReadByte(byte_addr, byte);
            if (status < 0) {
                CONSOLE_PRINTF("  ??");  // Indicate read failure with question marks.
            }
            CONSOLE_PRINTF("  %02x", byte);
        }
        CONSOLE_PRINTF("\r\n");  // End of page.
    }
}