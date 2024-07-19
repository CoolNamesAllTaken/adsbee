#ifndef EEPROM_HH_
#define EEPROM_HH_

#include "comms.hh"  // For debug logging.
#include "hardware/i2c.h"

class EEPROM {
   public:
    struct EEPROMConfig {
        i2c_inst_t *i2c_handle = i2c1;
        uint8_t i2c_addr = 0b1010001;  // M24C02, TSSOP-8, E3=0 E2=0 E1=1
        uint16_t size_bytes = 256;     // M24C02 = 2kb = 256B
        uint16_t page_size_bytes = 16;
        uint32_t i2c_timeout_us = 1e6;
        uint32_t i2c_write_time_us = 10e3;  // 5ms write time for Bytes and pages. 10ms for some buffer.

        bool requires_init = false;
        // These parameters only used if initialization is required.
        uint16_t onboard_i2c_sda_pin = 2;
        uint16_t onboard_i2c_scl_pin = 3;
        uint32_t onboard_i2c_clk_freq_hz = 400e3;  // 400kHz
    };

    /**
     * Constructor.
     * @param[in] config_in Configuration struct with parameters to use for EEPROM peripheral.
     */
    EEPROM(EEPROMConfig config_in) : config_(config_in){};

    /**
     * Initializes and tests the EEPROM. Optional (not required if I2C instance is already initialized).
     * @retval True if initialization was successful, false if there was an error.
     */
    bool Init();

    /**
     * Save an instance of an object to the EEPROM, stating at address start_addr.
     * @param[in] data_to_save Reference to the object to save in EEPROM.
     * @param[in] start_reg Optional register address for the start of the object. Defaults to 0x0.
     * @retval True if save succeeded, false otherwise.
     */
    template <typename T>  // Implemented here since implementing a template function in a .cc file is a pain.
    bool Save(const T &data_to_save, uint8_t start_reg = 0x0) {
        // Check size of data and available space on the EEPROM.
        uint16_t data_size_bytes = sizeof(data_to_save);
        uint16_t remaining_capacity_bytes = config_.size_bytes - start_reg;
        if (remaining_capacity_bytes < data_size_bytes) {
            CONSOLE_PRINTF(
                "EEPROM::Save: Failed to save data of size %d Bytes to EEPROM register 0x%x: only %d Bytes "
                "remaining.\r\n",
                data_size_bytes, start_reg, remaining_capacity_bytes);
            return false;
        }
        int num_bytes_written = WriteBuf(start_reg, (uint8_t *)(&data_to_save), data_size_bytes);
        if (num_bytes_written != data_size_bytes) {
            // num_bytes_written is usually the number of bytes written, but could be a negative error code value.
            CONSOLE_ERROR("EEPROM::Save: I2C write failed, written byte counter returned %d but expected %d.",
                          num_bytes_written, data_size_bytes);
            return false;
        }
        return true;
    }

    /**
     * Load an instance of an object from the EEPROM, starting at address start_addr.
     * @param[out] data_to_load Reference to the object to load data into.
     * @param[in] start_reg Optional register address for the start of the object. Defaults to 0x0.
     * @retval True if load succeeded, false otherwise.
     */
    template <typename T>  // Implemented here since implementing a template function in a .cc file is a pain.
    bool Load(T &data_to_load, uint8_t start_reg = 0x0) {
        uint16_t data_size_bytes = sizeof(data_to_load);
        uint16_t remaining_capacity_bytes = config_.size_bytes - start_reg;
        if (remaining_capacity_bytes < data_size_bytes) {
            CONSOLE_PRINTF(
                "EEPROM::Load: Failed to load data of size %d Bytes from EEPROM register 0x%x: only %d Bytes "
                "remaining.\r\n",
                data_size_bytes, start_reg, remaining_capacity_bytes);
            return false;
        }
        int num_bytes_read = ReadBuf(start_reg, (uint8_t *)(&data_to_load), sizeof(data_to_load));
        if (num_bytes_read != data_size_bytes) {
            // num_bytes_written is usually the number of bytes written, but could be a negative error code value.
            CONSOLE_ERROR("EEPROM::Save: I2C read failed, read byte counter returned %d but expected %d.",
                          num_bytes_read, data_size_bytes);
            return false;
        }
        return true;
    }

    int WriteByte(const uint16_t reg, const uint8_t byte);
    int ReadByte(const uint16_t reg, uint8_t &byte);

    /** I2C helper function that writes 1 byte to the specified register.
     * @param[in] reg Register address (on the device) to write to.
     * @param[in] buf Byte buffer to write to the given address.
     * @param[in] num_bytes Number of bytes to write to the given address on the device.
     * @retval Number of bytes that were written, or an error code. Should be equal to num_bytes+1 (includes 1-Byte
     * Address).
     */
    int WriteBuf(const uint16_t reg, uint8_t *buf, const uint16_t nbytes);

    /** Read byte(s) from the specified register. If num_bytes > 1, read from consecutive registers.
     * @param[in] reg Register address (on the device) to read from.
     * @param[in] buf Byte buffer to read into from the given address.
     * @param[in] num_bytes Number of bytes to read from the device.
     */
    int ReadBuf(const uint16_t reg, uint8_t *buf, const uint16_t nbytes);

    void Dump();

   private:
    EEPROMConfig config_;
    uint32_t last_write_timestamp_us_ = 0;

    /**
     * The EEPROM takes up to 5ms to write a Byte or page. This function gets called before a write operation to ensure
     * that we don't encounter errors by sending more data when the EEPROM isn't ready yet.
     */
    void WaitForSafeWriteTime();

    /**
     * Same as WaitForSafeWriteTime, but doesn't record the timestamp as last_write_timeestamp_us_.
     */
    void WaitForSafeReadTime();
};

extern EEPROM eeprom;

#endif