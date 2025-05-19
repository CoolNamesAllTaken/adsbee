#pragma once

#include "bsp.hh"
#include "hardware/spi.h"

class CC1312 {
   public:
    static const uint16_t kMaxNumPropertiesAtOnce = 12;
    static const uint32_t kCTSCheckIntervalUs = 40;
    static const uint32_t kBootupDelayMs = 100;
    static const uint32_t kSendCommandTimeoutMs = 100;

    struct CC1312Config {
        // This clock frequency is used to talk to the CC1312.
        uint32_t spi_clk_freq_hz = bsp.subg_spi_clk_freq_hz;
        spi_inst_t* spi_handle = bsp.copro_spi_handle;
        uint16_t spi_clk_pin = bsp.copro_spi_clk_pin;  // Pin for SPI clock (SCK).
        uint16_t spi_mosi_pin = bsp.copro_spi_mosi_pin;
        uint16_t spi_miso_pin = bsp.copro_spi_miso_pin;
        uint16_t spi_cs_pin = bsp.subg_cs_pin;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;
        uint16_t enable_pin = bsp.subg_enable_pin;  // Pin to enable the CC1312.
        uint16_t irq_pin = bsp.subg_irq_pin;        // Pin for CC1312 IRQ.
        uint16_t sync_pin = bsp.sync_pin;           // Pin for sync and CC1312 bootloader backdoor.
    };

    // The bootloader has a weird SPI configuration, so we need a struct to keep track of it.
    struct SPIPeripheralConfig {
        uint16_t bits_per_transfer = 8;
        spi_cpol_t cpol = SPI_CPOL_0;
        spi_cpha_t cpha = SPI_CPHA_0;
        spi_order_t order = SPI_MSB_FIRST;
    };

    enum ProtocolByte : uint8_t {
        kProtocolByteAck = 0xCC,
        kProtocolByteNack = 0x33,
    };

    enum Command : uint8_t {
        kCmdPing = 0x20,
        kCmdDownload = 0x21,
        kCmdGetStatus = 0x23,
        kCmdSendData = 0x24,
        kCmdReset = 0x25,
        kCmdSectorErase = 0x26,
        kCmdCRC32 = 0x27,
        kCmdGetChipID = 0x26,
        kCmdMemoryRead = 0x2A,
        kCmdMemoryWrite = 0x28,
        kCmdBankErase = 0x2C,
        kCmdSetCCFG = 0x2D,
        kCmdDownloadCRC = 0x2F
    };

    enum CommandReturnStatus : uint8_t {
        kCmdRetSuccess = 0x40,     // Status for successful command.
        kCmdRetUnknownCmd = 0x41,  // Status for unknown command.
        kCmdRetInvalidCmd = 0x42,  // Status for invlaid command (in other words, incorrect packet size).
        kCmdRetInvalidAdr = 0x43,  // Status for invalid input address.
        kCmdRetFlashFail = 0x44    // Status for failing flash erase or program operation.
    };

    const char* CommandReturnStatusToString(CommandReturnStatus status) {
        switch (status) {
            case kCmdRetSuccess:
                return "Success";
            case kCmdRetUnknownCmd:
                return "Unknown command";
            case kCmdRetInvalidCmd:
                return "Invalid command";
            case kCmdRetInvalidAdr:
                return "Invalid address";
            case kCmdRetFlashFail:
                return "Flash fail";
            default:
                return "Unknown status";
        }
    }

    /**
     * Adjusts the SPI peripheral to be able to talk to the CC1312. Nominally adjusts clock rate, but also adjusts CPHA
     * and CPOL if the bootloader is active.
     */
    void SPIBeginTransaction();
    /**
     * Restores the SPI peripheral to its previous state. Nominally restores clock rate, but also restores CPHA and CPOL
     * if the bootloader is active.
     */
    void SPIEndTransaction();
    int SPIWriteReadBlocking(uint8_t* tx_buf, uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true);
    inline int SPIWriteBlocking(uint8_t* tx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(tx_buf, nullptr, len_bytes, end_transaction);
    }
    inline int SPIReadBlocking(uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(nullptr, rx_buf, len_bytes, end_transaction);
    }

    /**
     * Constructor for CC1312.
     * @param[in] config_in Configuration struct for the CC1312.
     */
    CC1312(CC1312Config config_in) : config_(config_in) {};

    /**
     * Destructor for CC1312.
     */
    ~CC1312();

    /**
     * Initialize CC1312.
     * @param[in] spi_already_initialized Set to true if using a shared SPI bus such that the SPI bus is already
     * initialized.
     */
    bool Init(bool spi_already_initialized = false);

    /**
     * Verifies that the last command sent to the CC1312 bootloader was successful by sending a COMMAND_GET_STATUS
     * command and checking that the value returned is COMMAND_RET_SUCCESS.
     */
    bool BootloaderLastCommandSucceeded();

    /**
     * Sends a COMMAND_PING to the CC1312 in bootloader mode, and returns true if an ACK is received.
     * @retval True if the CC1312 is in bootloader mode, false otherwise.
     */
    bool BootloaderPing();

    bool BootloaderReceiveBuffer(uint8_t* buf, uint16_t buf_len_bytes);
    bool BootloaderSendBuffer(uint8_t* buf, uint16_t buf_len_bytes);

    /**
     * Brings the CC1312 into bootloader mode and sets the SPI peripheral to be able to communicate with the CC1312.
     * NOTE: SPI peripheral uses CPOL=1, CPHA=1 in bootloader mode, CPOL=0, CPHA=0 in normal mode.
     */
    bool EnterBootloader();

    bool ExitBootloader();

    /**
     * Set the enable pin.
     * @param[in] enabled True to enable the CC1312, false to disable.
     */
    inline void SetEnable(bool enabled) {
        // Enable is active HI
        gpio_put(config_.enable_pin, enabled);
        enabled_ = enabled;
    }

    /**
     * Returns whether the CC1312 is currently enabled.
     * @retval True if enabled, false otherwise.
     */
    inline bool IsEnabled() { return enabled_; }

   private:
    CC1312Config config_;
    bool enabled_ = false;
    bool in_bootloader_ = false;

    // Clock config struct used to set the SPI peripheral to the correct clock rate.
    struct SPIClkConfig {
        uint prescale = 0;
        uint postdiv = 0;
    };
    SPIClkConfig standby_clk_config_;
    SPIClkConfig active_clk_config_;

    /**
     * Helper function that stores the current SPI clock configuration for a SPI peripheral.
     * @retval SPIClkConfig struct with the SPI clock parameters.
     */
    inline SPIClkConfig spi_get_clk() {
        return {
            .prescale = spi_get_const_hw(config_.spi_handle)->cpsr,
            .postdiv = ((spi_get_const_hw(config_.spi_handle)->cr0 & SPI_SSPCR0_SCR_BITS) >> SPI_SSPCR0_SCR_LSB) + 1};
    }

    /**
     * Helper function that restores a SPI clock configuration for a SPI peripheral.
     * @param[in] clk_config SPI clock configuration to restore.
     */
    inline void spi_set_clk(const SPIClkConfig& clk_config) {
        spi_get_hw(config_.spi_handle)->cpsr = clk_config.prescale;
        hw_write_masked(&spi_get_hw(config_.spi_handle)->cr0, (clk_config.postdiv - 1) << SPI_SSPCR0_SCR_LSB,
                        SPI_SSPCR0_SCR_BITS);
    }
};