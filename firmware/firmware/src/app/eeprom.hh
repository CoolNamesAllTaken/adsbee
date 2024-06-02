#ifndef EEPROM_HH_
#define EEPROM_HH_

#include "comms.hh"  // For debug logging.
#include "hardware/i2c.h"

class EEPROM {
   public:
    struct EEPROMConfig {
        i2c_inst_t *i2c_handle = i2c1;
        uint8_t i2c_addr = 0b1010001;  // M24C02, TSSOP-8, E3=0 E2=0 E1=1
        uint16_t size_bytes = 2e3;     // M24C02 = 2kB
        uint16_t page_size_bytes = 16;
        uint32_t i2c_timeout_us = 1e6;

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
    template <typename T>
    bool Save(const T &data_to_save, uint8_t start_reg = 0x0);

    /**
     * Load an instance of an object from the EEPROM, starting at address start_addr.
     * @param[out] data_to_load Reference to the object to load data into.
     * @param[in] start_reg Optional register address for the start of the object. Defaults to 0x0.
     * @retval True if load succeeded, false otherwise.
     */
    template <typename T>
    bool Load(T &data_to_load, uint8_t start_reg = 0x0);

    int WriteByte(const uint8_t reg, const uint8_t byte);
    int ReadByte(const uint8_t reg, uint8_t &byte);

    /** I2C helper function that writes 1 byte to the specified register.
     * @param[in] reg Register address (on the device) to write to.
     * @param[in] buf Byte buffer to write to the given address.
     * @param[in] num_bytes Number of bytes to write to the given address on the device.
     * @retval Number of bytes that were written, or an error code. Should be equal to num_bytes+1 (includes 1-Byte
     * Address).
     */
    inline int WriteBuf(const uint8_t reg, uint8_t *buf, const uint16_t nbytes);

    /** Read byte(s) from the specified register. If num_bytes > 1, read from consecutive registers.
     * @param[in] reg Register address (on the device) to read from.
     * @param[in] buf Byte buffer to read into from the given address.
     * @param[in] num_bytes Number of bytes to read from the device.
     */
    inline int ReadBuf(const uint8_t reg, uint8_t *buf, const uint16_t nbytes);

   private:
    EEPROMConfig config_;
};

extern EEPROM eeprom;

#endif