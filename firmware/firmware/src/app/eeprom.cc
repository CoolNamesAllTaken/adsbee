#include "eeprom.hh"

#include <cmath>
#include <cstring>

#include "hardware/gpio.h"  // For optional I2C initialization.
#include "hardware/i2c.h"

inline int EEPROM::WriteByte(const uint8_t reg, const uint8_t byte) {
    uint8_t msg[2];
    msg[0] = reg;
    msg[1] = byte;
    return i2c_write_blocking(config_.i2c_handle, config_.i2c_addr, &msg, 2, false);
}
inline int EEPROM::ReadByte(const uint8_t reg, uint8_t &byte) {
    // Write address to read from.
    int status = i2c_write_blocking(config_.i2c_handle, addr, &reg, 1, true);
    if (status < 0) return status;
    // Read reply and put it into byte.
    return i2c_read_blocking(config_.i2c_handle, config_.i2c_addr, &byte, 1, false);
}

inline int EEPROM::WriteBuf(const uint8_t reg, uint8_t *buf, uint16_t num_bytes) {
    // Check to make sure caller is sending 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }

    uint8_t write_reg = reg;
    uint16_t num_bytes_written = 0;
    while (num_bytes_written < num_bytes) {
        uint8_t page_bytes_remaining = config_.page_size_bytes - (reg % config_.page_size_bytes);
        uint8_t write_num_bytes = min(page_bytes_remaining, num_bytes - num_bytes_written);
        uint8_t msg[write_num_bytes + 1];  // Add a spot for the address.
        msg[0] = write_reg;
        for (uint16_t i = 0; i < write_num_bytes; i++) {
            msg[i + 1] = buf[num_bytes_written + i];
        }
        bool is_last_write = (num_bytes_written + write_num_bytes) == num_bytes;
        // Don't give up control of the bus until done writing the payload.
        int status = i2c_write_blocking(config_.i2c_handle, config_.i2c_addr, msg, write_num_bytes + 1, !is_last_write);
        if (status < 0) {
            DEBUG_PRINTF("EEPROM::I2CRegWrite: Write failed at register 0x%x while trying to write %d bytes.\r\n",
                         write_reg, write_num_bytes);
            return status;
        }
        num_bytes_written += write_num_bytes;
    }

    return num_bytes;
}

inline int EEPROM::ReadBuf(const uint8_t reg, uint8_t *buf, const uint16_t num_bytes) {
    int num_bytes_read = 0;

    // Check to make sure caller is asking for 1 or more bytes
    if (num_bytes < 1) {
        return 0;
    }

    // Read data from register(s) over I2C
    i2c_write_blocking(config_.i2c_handle, addr, &reg, 1, true);
    num_bytes_read = i2c_read_blocking(config_.i2c_handle, config_.i2c_addr, buf, num_bytes, false);

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
    if (i2c_read_blocking(config_.i2c_handle, config_.i2c_addr, &eeprom_random_address_data, 1, false) != 1) {
        DEBUG_PRINTF("EEPROM::Init: Failed to read current address from EEPROM at I2C address 0x%x.\r\n",
                     config_.i2c_addr);
        return false;
    }
    return true;
}

template <typename T>
bool EEPROM::Save(const T &data_to_save, uint8_t start_reg) {
    // Check size of data and available space on the EEPROM.
    uint16_t data_size_bytes = sizeof(data_to_save);
    uint16_t remaining_capacity_bytes = config_.size_bytes - start_reg;
    if (remaining_capacity_bytes < data_size_bytes) {
        DEBUG_PRINTF(
            "EEPROM::Save: Failed to save data of size %d Bytes to EEPROM register 0x%x: only %d Bytes remaining.\r\n",
            data_size_bytes, start_reg, remaining_capacity_bytes);
        return false;
    }
    int num_bytes_written = WriteBuf(config_.i2c_handle, config_.i2c_addr, (uint8_t *)(&data_to_save), data_size_bytes);
    int expected_bytes_written = data_size_bytes + 1;
    if (num_bytes_written != expected_bytes_written) {
        // num_bytes_written is usually the number of bytes written, but could be a negative error code value.
        DEBUG_PRINTF("EEPROM::Save: I2C write failed, written byte counter returned %d but expected %d.\r\n");
        return false;
    }
    return true;
}

template <typename T>
bool EEPROM::Load(T &data_to_load, uint8_t start_reg) {
    uint16_t data_size_bytes = sizeof(data_to_save);
    uint16_t remaining_capacity_bytes = config_.size_bytes - start_reg;
    if (remaining_capacity_bytes < data_size_bytes) {
        DEBUG_PRINTF(
            "EEPROM::Load: Failed to load data of size %d Bytes from EEPROM register 0x%x: only %d Bytes "
            "remaining.\r\n",
            data_size_bytes, start_reg, remaining_capacity_bytes);
        return false;
    }
}

CPP_AT_CALLBACK(EEPROM::EEPROMTestCallback) {
    DEBUG_PRINTF("[EEPROMTest BasicWriteReadByte\r\n");
    assert(WriteByte(0x0, 0xDE));
    assert(WriteByte(0x1, 0xAD));
    assert(WriteByte(0x2, 0xBE));
    assert(WriteByte(0x3, 0xEF));
    uint8_t byte;
    assert(ReadByte(0x0, byte));
    assert(byte == 0xDE);
    assert(ReadByte(0x1, byte));
    assert(byte == 0xAD);
    assert(ReadByte(0x2, byte));
    assert(byte == 0xBE);
    assert(ReadByte(0x3, byte));
    assert(byte == 0xEF);
    DEBUG_PRINTF("PASS]\r\n")
}