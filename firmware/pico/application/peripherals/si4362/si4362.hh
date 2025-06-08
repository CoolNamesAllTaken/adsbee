#pragma once

#include "bsp.hh"
#include "hardware/spi.h"

class Si4362 {
   public:
    static const uint16_t kMaxNumPropertiesAtOnce = 12;
    static const uint32_t kCTSCheckIntervalUs = 40;
    static const uint32_t kBootupDelayMs = 100;
    static const uint32_t kSendCommandTimeoutMs = 100;

    struct Si4362Config {
        // This clock frequency is used to talk to the Si4362.
        uint32_t spi_clk_freq_hz = bsp.r978_spi_clk_freq_hz;
        spi_inst_t* spi_handle = bsp.copro_spi_handle;
        uint16_t spi_clk_pin = bsp.copro_spi_clk_pin;  // Pin for SPI clock (SCK).
        uint16_t spi_mosi_pin = bsp.copro_spi_mosi_pin;
        uint16_t spi_miso_pin = bsp.copro_spi_miso_pin;
        uint16_t spi_cs_pin = bsp.r978_cs_pin;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;
        uint16_t enable_pin = bsp.r978_enable_pin;  // Pin to enable the Si4362.
        uint16_t irq_pin = bsp.r978_irq_pin;        // Pin for Si4362 IRQ.
    };

    enum Command : uint8_t {
        // Boot Commands
        kCmdPowerUp = 0x02,  // Command to power up the device and select the operational mode and functionality.

        // Common Commands
        kCmdNop = 0x00,          // No operation command.
        kCmdPartInfo = 0x01,     // Reports basic information about the device.
        kCmdFuncInfo = 0x10,     // Returns the Function revision information of the device.
        kCmdSetProperty = 0x11,  // Sets the value of one or more properties.
        kCmdGetProperty = 0x12,  // Retrieves the value of one or more properties.
        kCmdGPIOPinCfg = 0x13,   // Configures the GPIO pins.
        kCmdFIFOInfo =
            0x15,  // Access the current byte counts in the TX and RX FIFOs and provide for resetting the FIFOs.
        kCmdGetINTStatus =
            0x20,  // Returns the interrupt status of ALL the possible interrupt events (both STATUS and PENDING).
        kCmdRequestDeviceState = 0x33,  // Request current device state and channel.
        kCmdChangeState = 0x34,         // Manually switch the chip to a desired operating state.
        kCmdOfflineRecal = 0x38,        // Recalibrates due to temperature change.
        kCmdReadCmdBuff = 0x44,         // Used to read CTS and the command response.
        kCmdFRRARead = 0x50,            // Reads the fast response registers (FRR) starting with FRR_A.
        kCmdFRRBRead = 0x51,            // Reads the fast response registers (FRR) starting with FRR_B.
        kCmdFRRCRead = 0x53,            // Reads the fast response registers (FRR) starting with FRR_C.
        kCmdFRRDRead = 0x57,            // Reads the fast response registers (FRR) starting with FRR_D.

        // IR Cal Commands
        kCmdIRCal = 0x17,        // Image rejection calibration.
        kCmdIRCalManual = 0x19,  // Image rejection calibration.

        // TX Commands
        kCmdStartTx = 0x31,      // Switches to TX state and starts transmission of a packet.
        kCmdTXHop = 0x37,        // Hop to a new frequency while in TX.
        kCmdWriteTxFIFO = 0x66,  // Writes data byte(s) to the TX FIFO.

        // RX Commands
        kCmdPacketInfo =
            0x16,  // Returns information about the length of the variable field in the last packet received.
        kCmdGetModemStatus = 0x22,  // Returns the interrupt status of the Modem Interrupt Group.
        kCmdStartRx = 0x32,         // Switches to RX state and starts reception of a packet.
        kCmdRXHop = 0x36,           // Manually hop to a new frequency while in RX mode.
        kCmdReadRxFIFO = 0x77,      // Reads data byte(s) from the RX FIFO.

        // Advanced Commands
        kCmdGetADCReading = 0x14,  // Performs conversions using the Auxiliary ADC and returns the results.
        kCmdGetPHStatus = 0x21,    // Returns the interrupt status of the Packet Handler Interrupt Group.
        kCmdGetChipStatus = 0x23,  // Returns the interrupt status of the Chip Interrupt Group.
    };

    enum Group : uint8_t {
        kGroupGlobal = 0x00,
        kGroupInterrupt = 0x01,
        kGroupFastResponseRegister = 0x02,
        kGroupPreamble = 0x10,
        kGroupSync = 0x11,
        kGroupPacket = 0x12,
        kGroupModem = 0x20,
        kGroupModemChannelFilter = 0x21,
        kGroupSynthesizer = 0x23,
        kGroupMatch = 0x30,
        kGroupFrequencyControl = 0x40,
        kGroupReceiverHop = 0x50,
        kGroupPacketTraceInterface = 0xf0
    };

    enum DeviceState : uint8_t {
        kStateInvalid = 0,
        kStateSleep = 1,
        kStateSPIActive = 2,
        kStateReady = 3,
        kStateReady2 = 4,
        kStateRxTune = 6,
        kStateRx = 8
    };

    enum RxTimeoutState : uint8_t {
        kRxTimeoutStateNoChange = 0,
        kRxTimeoutStateSleep = 1,
        kRxTimeoutStateSPIActive = 2,
        kRxTimeoutStateReady = 3,
        kRxTimeoutStateReady2 = 4,
        kRxTimeoutStateRxTune = 6,
        kRxTimeoutStateRx = 8,
        kRxTimeoutStateRxIdle = 9
    };

    enum PostRxState : uint8_t {
        kPostRxStateRemain = 0,
        kPostRxStateSleep = 1,
        kPostRxStateSPIActive = 2,
        kPostRxStateReady = 3,
        kPostRxStateReady2 = 4,
        kPostRxStateRxTune = 6,
        kPostRxStateRx = 8
    };

    // This struct contains configurations that are applied on top of the default modem config values generated by WDS.
    struct ModemConfig {
        /** MODEM_CONFIG **/
        uint32_t data_rate = 1041667 * 10;  // UAT data rate with 10x oversampling.
        // MODEM_DECIMATION_CFG1: 0x20 [0x1e]
        uint8_t ndec2;  // 2 bits
        uint8_t ndec1;  // 2 bits
        uint8_t ndec0;  // 3 bits
        // MODEM_DECIMATION_CFG0: 0x20 [0x1f]
        bool chflt_lopw;   // Reduce power and reduce digital filter from 27 taps to 15 taps (wider bandwidth).
        bool droopfltbyp;  // Bypass the droop compensation filter.
        bool dwn3byp;      // Bypass additional 2x decimator.
        bool dwn2byp;      // Bypass additional 2x decimator.
        bool rxgain2;      // Double the decimate-by-8 filter gain.
        // MODEM_DECIMATION_CFG2
        uint8_t ndec3;      // 3 bits
        uint8_t ndec2gain;  // 2 bits
        bool ndec2agc;      // 1 bit
        // MODEM_IFPKD_THRESHOLDS
        // MODEM_BCR_OSR: 0x20 [0x22-0x23]
        uint8_t rxosr;  // 12 bits: 8x the desired RX oversampling rate.
        // MODEM_BCR_NCO_OFFSET: 0x20 [0x24-0x26]
        uint32_t ncoff;  // 24 bits
        // MODEM_BCR_GAIN: Gain of bit recovery loop for rx phase alignment.
        // MODEM_BCR_GEAR: Select between fast and slow bit recovery gears.
        // MODEM_BCR_MISC1
        // MODEM_BCR_MISC0

        void print();
    };

    int SPIWriteReadBlocking(uint8_t* tx_buf, uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true);
    inline int SPIWriteBlocking(uint8_t* tx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(tx_buf, nullptr, len_bytes, end_transaction);
    }
    inline int SPIReadBlocking(uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(nullptr, rx_buf, len_bytes, end_transaction);
    }

    bool SetDeviceState(DeviceState state, bool verify = false);

    /**
     * Helper function that checks whether the radio has processed its previous command and is ready to receive another.
     * @param[in] end_transaction Set to true to end the SPI transaction after checking. If false, SPI transaction will
     * only be ended if the CTS value is not 0xFF.
     */
    bool ClearToSend(bool end_transaction = true);

    /**
     * Returns the name of a given device state as a c-string.
     * @param[in] state Device state to convert to a string.
     * @retval Pointer to the string representation of the device state.
     */
    inline char* DeviceStateToString(const DeviceState& state) {
        switch (state) {
            case kStateInvalid:
                return (char*)"Invalid";
            case kStateSleep:
                return (char*)"Sleep";
            case kStateSPIActive:
                return (char*)"SPI Active";
            case kStateReady:
                return (char*)"Ready";
            case kStateReady2:
                return (char*)"Ready 2";
            case kStateRxTune:
                return (char*)"RX Tune";
            case kStateRx:
                return (char*)"RX";
            default:
                return (char*)"Unknown";
        }
    }

    /**
     * Returns the configuration of modem parameters that are manually overrode over the default WDS configuration.
     * @param[in] modem_config Reference to the modem config struct to fill.
     * @retval True if the modem config was got successfully, false otherwise.
     */
    bool GetModemConfig(ModemConfig& modem_config);

    /**
     * Get a property or group of properties from the Si4362. Can get up to 12 properties at once.
     * @param[in] group Property group to get.
     * @param[in] num_props Number of properties to get.
     * @param[in] start_prop First property to get.
     * @param[out] data Pointer to the data to get.
     * @retval True if the properties were got successfully, false otherwise.
     */
    bool GetProperty(Group group, uint8_t num_props, uint8_t start_prop, uint8_t* data);

    /**
     * Request the current state of the modem and the channel.
     * @param[out] state Current state of the modem.
     * @param[out] channel Current channel of the modem.
     * @retval True if the state was requested successfully, false otherwise.
     */
    inline bool GetDeviceState(DeviceState& state, uint8_t& channel) {
        uint8_t reply[2];
        bool ret = ReadCommand(kCmdRequestDeviceState, reply, sizeof(reply));
        if (ret) {
            state = static_cast<DeviceState>(reply[0] & 0xF);
            channel = reply[1];
        }
        return ret;
    }

    /**
     * Send a command to the Si4362.
     * @param[in] cmd Command to send.
     * @param[in] param_buf Optional parameter buffer to send with the command. Can be null.
     * @param[in] param_buf_len Length of the parameter buffer.
     * @param[in] pre_block_until_cts Poll for CTS before sending the command. Normally this is a good idea, unless the
     * Chip hasn't been booted yet. Defaults to true.
     * @param[in] post_block_until_cts Set to true to block until the command is complete. If false, the command will be
     * sent and the function will return immediately. Defaults to false.
     * @param[in] end_transaction Set to true to end the SPI transaction after sending the command. If false, SPI
     * transaction will only be ended if the CTS value is not 0xFF.
     * @retval True if the command was sent successfully, false otherwise.
     */
    bool SendCommand(Command cmd, const uint8_t* param_buf = nullptr, uint16_t param_buf_len = 0,
                     bool pre_block_until_cts = true, bool post_block_until_cts = false, bool end_transaction = true);

    /**
     * Sends a data array in the format that is generated by WDS. The data array is a continuous sequence of sub-arrays
     * of Bytes. Each sub-array has a 1-byte value for the number of Bytes to send, followed by the Bytes to send.
     * @param [in] data Pointer to the data to send.
     * @param [in] len_bytes Length of the data to send.
     * @retval True if the data was sent successfully, false otherwise.
     */
    bool SendDataArray(const uint8_t* data, uint16_t len_bytes);

    bool SetModemConfig(const ModemConfig& modem_config);

    /**
     * Sets a property or group of properties on the Si4362. Can set up to 12 properties at onece. Length of data must
     * match value of num_props.
     * @param[in] group Property group to set.
     * @param[in] num_props Number of properties to set.
     * @param[in] start_prop First property to set.
     * @param[in] data Pointer to the data to set.
     * @retval True if the properties were set successfully, false otherwise.
     */
    bool SetProperty(Group group, uint8_t num_props, uint8_t start_prop, uint8_t* data);

    // TODO: Change default values for PostRxState to not loop continuously.
    /**
     * Start receiving packets.
     * @param[in] channel Channel to start receiving on.
     * @param[in] update Set to true to update rx parameters but not enter rx mode. False to enter RX mode immediately.
     * @param[in] start Set to true to start receiving immediately. False to update when the wakeup timer expires.
     * @param[in] rx_len Length of the packet to receive. Uses default packet length if set to 0. 13 bits.
     * @param[in] rxtimeout_state State to enter when the RX timeout occurs. Defaults to no change.
     * @param[in] rxvalid_state State to enter when a valid packet is received. Defaults to RX.
     * @param[in] rxinvalid_state State to enter when an invalid packet is received. Defaults to RX.
     * @retval True if the RX was started successfully, false otherwise.
     */
    bool StartRx(uint8_t channel = 0, bool update = false, bool start = 0, uint16_t rx_len = 0,
                 RxTimeoutState rxtimeout_state = kRxTimeoutStateNoChange, PostRxState rxvalid_state = kPostRxStateRx,
                 PostRxState rxinvalid_state = kPostRxStateRx);

    /**
     * Read a command from the Si4362.
     * @param[in] cmd Command to read.
     * @param[in] response_buf Buffer to store the command response.
     * @param[in] response_buf_len Length of the parameter buffer.
     * @param[in] command_buf Optional command buffer to send with the command. Can be null.
     * @param[in] command_buf_len Length of the command buffer.
     * @retval True if the command was read successfully, false otherwise.
     */
    bool ReadCommand(Command cmd, uint8_t* response_buf, uint16_t response_buf_len, uint8_t* command_buf = nullptr,
                     uint16_t command_buf_len = 0);

    /**
     * Constructor for Si4362.
     * @param[in] config_in Configuration struct for the Si4362.
     */
    Si4362(Si4362Config config_in) : config_(config_in) {};

    /**
     * Destructor for Si4362.
     */
    ~Si4362();

    /**
     * Initialize Si4362.
     * @param[in] spi_already_initialized Set to true if using a shared SPI bus such that the SPI bus is already
     * initialized.
     */
    bool Init(bool spi_already_initialized = false);

    /**
     * Set the enable pin.
     * @param[in] enabled True to enable the Si4362, false to disable.
     */
    inline void SetEnable(bool enabled) {
        // Enable is active LO since the enable pin is actually a shutdown pin.
        gpio_put(config_.enable_pin, !enabled);
        enabled_ = enabled;
    }

    /**
     * Returns whether the Si4362 is currently enabled.
     * @retval True if enabled, false otherwise.
     */
    inline bool IsEnabled() { return enabled_; }

   private:
    Si4362Config config_;
    bool enabled_ = false;
    uint32_t last_cts_check_us_ = 0;

    // Clock config struct used to set the SPI peripheral to the correct clock rate.
    struct spi_clk_config {
        uint prescale = 0;
        uint postdiv = 0;
    };
    spi_clk_config standby_clk_config_;
    spi_clk_config active_clk_config_;

    /**
     * Helper function that stores the current SPI clock configuration for a SPI peripheral.
     * @retval spi_clk_config struct with the SPI clock parameters.
     */
    inline spi_clk_config spi_get_clk() {
        return {
            .prescale = spi_get_const_hw(config_.spi_handle)->cpsr,
            .postdiv = ((spi_get_const_hw(config_.spi_handle)->cr0 & SPI_SSPCR0_SCR_BITS) >> SPI_SSPCR0_SCR_LSB) + 1};
    }

    /**
     * Helper function that restores a SPI clock configuration for a SPI peripheral.
     * @param[in] clk_config SPI clock configuration to restore.
     */
    inline void spi_set_clk(const spi_clk_config& clk_config) {
        spi_get_hw(config_.spi_handle)->cpsr = clk_config.prescale;
        hw_write_masked(&spi_get_hw(config_.spi_handle)->cr0, (clk_config.postdiv - 1) << SPI_SSPCR0_SCR_LSB,
                        SPI_SSPCR0_SCR_BITS);
    }
};