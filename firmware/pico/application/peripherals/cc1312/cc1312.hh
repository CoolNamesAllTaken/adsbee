#pragma once

#include "bsp.hh"
#include "comms.hh"
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
        kCmdRetDriverError = 0x00,  // Made up (non-TI status) for indicating a generic error in our code.
        kCmdRetSuccess = 0x40,      // Status for successful command.
        kCmdRetUnknownCmd = 0x41,   // Status for unknown command.
        kCmdRetInvalidCmd = 0x42,   // Status for invlaid command (in other words, incorrect packet size).
        kCmdRetInvalidAdr = 0x43,   // Status for invalid input address.
        kCmdRetFlashFail = 0x44     // Status for failing flash erase or program operation.
    };

    const char* CommandReturnStatusToString(CommandReturnStatus status) {
        switch (status) {
            case kCmdRetDriverError:
                return "Driver error";
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

    // CCFG field IDs used to set CCFG values via memory mapped CCFG registers.
    enum BootloaderCCFGFieldID : uint32_t {
        kCCFGFieldIDSectorProt = 0,  // Flash sector number of sector to protect from program and erase.
        kCCFGFieldIDImageValid = 1,  // Address of flash image vector table to allow jump to application.
        kCCFGFieldIDTestTAPOLck = 2,
        kCCFGFieldIDPwrprofTAPLck = 3,
        kCCFGFieldIDCPUDAPLck = 4,
        kCCFGFieldIDAONTAPLck = 5,
        kCCFGFieldIDPBIST1TAPLck = 6,
        kCCFGFieldIDPBIST2TAPLck = 7,
        kCCFGFieldIDIDBankEraseDis = 8,  // Set to 0 to disable bank erase from bootloader using COMMAND_BANK_ERASE.
        kCCFGFieldIDChipEraseDis = 9,    // Set to 0 to disable any chip erase operation.
        kCCFGFieldIDTIFAEnable = 10,     // Set to non-0x5 value to disable TI FA in following boot.
        kCCFGFieldIDBLBackdoorEn = 11,   // Set to non-0x5 to disable bootloader backdoor in following boot.
        kCCFGFieldIDBLBackdoorPin = 12,  // Set to DIO pin number to use for bootloader backdoor. Must be in Bit[7:0].
        kCCFGFieldIDBackdoorLevel = 13,  // Set to the active level of the bootloader backdoor pin. Must be in Bit[0].
        kCCFGFieldIDBLEnable = 14        // Set to non-0x5 to disable the bootloader.
    };

    struct BootloaderCCFGConfig {
        // Note: Struct only includes the CCFG fields that we are interested in.
        bool bank_erase_disabled = false;
        bool chip_erase_disabled = false;
        bool bl_backdoor_enabled = true;
        uint8_t bl_backdoor_pin = bsp.subg_bootloader_backdoor_pin;
        bool bl_backdoor_level = true;  // Active high.
        bool bl_enabled = true;         // Bootloader enabled.
    };

    // Register offsets used to read CCFG values from memory.
    enum BootloaderCCFGRegisterOffset : uint16_t {
        kCCFGRegOffExtLFClk = 0x1FA8,         // External LF clock configuration
        kCCFGRegOffModeConf1 = 0x1FAC,        // Mode Configuration 1
        kCCFGRegOffSizeAndDisFlags = 0x1FB0,  // CCFG Size and Disable Flags
        kCCFGRegOffModeConf = 0x1FB4,         // Mode Configuration 0
        kCCFGRegOffVoltLoad0 = 0x1FB8,        // Voltage Load 0
        kCCFGRegOffVoltLoad1 = 0x1FBC,        // Voltage Load 1
        kCCFGRegOffRTCOffset = 0x1FC0,        // Real Time Clock Offset
        kCCFGRegOffFreqOffset = 0x1FC4,       // Frequency Offset
        kCCFGRegOffIEEEMac0 = 0x1FC8,         // IEEE MAC Address 0
        kCCFGRegOffIEEEMac1 = 0x1FCC,         // IEEE MAC Address 1
        kCCFGRegOffIEEEBLE0 = 0x1FD0,         // IEEE BLE Address 0
        kCCFGRegOffIEEEBLE1 = 0x1FD4,         // IEEE BLE Address 1
        kCCFGRegOffBLConfig = 0x1FD8,         // Bootloader Configuration
        kCCFGRegOffEraseConf = 0x1FDC,        // Erase Configuration
        kCCFGRegOffTIOptions = 0x1FE0,        // TI Options
        kCCFGRegOffTapDap0 = 0x1FE4,          // Test Access Points Enable 0
        kCCFGRegOffTapDap1 = 0x1FE8,          // Test Access Points Enable 1
        kCCFGRegOffImageValidConf = 0x1FEC,   // Image Valid
        kCCFGRegOffProt31_0 = 0x1FF0,         // Protect Sectors 0-31
        kCCFGRegOffProt63_32 = 0x1FF4,        // Protect Sectors 32-63
        kCCFGRegOffProt95_64 = 0x1FF8,        // Protect Sectors 64-95
        kCCFGRegOffProt127_96 = 0x1FFC        // Protect Sectors 96-127
    };

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
    CommandReturnStatus BootloaderCommandGetStatus();

    template <typename T>
    bool BootloaderCommandMemoryRead(uint32_t address, T* buf, uint8_t buf_len) {
        static_assert(std::is_same<T, uint32_t>::value || std::is_same<T, uint8_t>::value,
                      "T must be either uint32_t or uint8_t");

        bool is_32bit = sizeof(T) == 4;
        // If explicit is_32bit doesn't match the template type, show a warning but respect the explicit parameter
        if (is_32bit != is_32bit) {
            CONSOLE_ERROR("CC1312::BootloaderCommandMemoryRead",
                          "Warning: is_32bit parameter (%d) doesn't match template type size (%d bytes)",
                          is_32bit ? 1 : 0, sizeof(T));
        }

        if ((is_32bit && buf_len > 63) || (!is_32bit && buf_len > 253)) {
            CONSOLE_ERROR("CC1312::BootloaderCommandMemoryRead", "Buffer length too large, max is %d.",
                          is_32bit ? 63 : 253);
            return false;
        }
        uint8_t cmd_buf[] = {kCmdMemoryRead,
                             static_cast<uint8_t>((address >> 24) & 0xFFu),
                             static_cast<uint8_t>((address >> 16) & 0xFFu),
                             static_cast<uint8_t>((address >> 8) & 0xFFu),
                             static_cast<uint8_t>(address & 0xFFu),
                             static_cast<uint8_t>(is_32bit ? 0x01u : 0x00u),  // 1 for 32-bit, 0 for 8-bit.
                             buf_len};

        if (!BootloaderSendBuffer(cmd_buf, sizeof(cmd_buf))) {
            CONSOLE_ERROR("CC1312::BootloaderCommandMemoryRead", "Failed to send memory read command.");
            return false;
        }

        uint8_t data_buf[is_32bit ? 4 * buf_len : buf_len] = {0};
        if (!BootloaderReceiveBuffer(data_buf, sizeof(data_buf))) {
            CONSOLE_ERROR("CC1312::BootloaderCommandMemoryRead", "Failed to receive reply to memory read command.");
            return false;
        }

        if (is_32bit) {
            for (uint8_t i = 0; i < buf_len; i++) {
                buf[i] = static_cast<T>((data_buf[4 * i] << 24) | (data_buf[4 * i + 1] << 16) |
                                        (data_buf[4 * i + 2] << 8) | data_buf[4 * i + 3]);
            }
        } else {
            for (uint8_t i = 0; i < buf_len; i++) {
                buf[i] = static_cast<T>(data_buf[i]);
            }
        }
        return true;
    }

    /**
     * Sends a COMMAND_PING to the CC1312 in bootloader mode, and returns true if an ACK is received.
     * @retval True if the CC1312 is in bootloader mode, false otherwise.
     */
    bool BootloaderCommandPing();

    /**
     * Initiates a reset of the CC1312. Used t boot into a new app after flashing.
     * @retval True if the command was ACKed (no get status check), false otherwise.
     */
    bool BootloaderCommandReset();

    bool BootloaderReadCCFGConfig(BootloaderCCFGConfig& ccfg_config);
    bool BootloaderWriteCCFGConfig(const BootloaderCCFGConfig& ccfg_config);

    bool BootloaderReceiveBuffer(uint8_t* buf, uint16_t buf_len_bytes);
    bool BootloaderSendBuffer(uint8_t* buf, uint16_t buf_len_bytes);
    bool BootloaderSendBufferCheckSuccess(uint8_t* buf, uint16_t buf_len_bytes);

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