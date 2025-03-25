#pragma once

#include "bsp.hh"
#include "hardware/spi.h"

class Si4362 {
   public:
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
        kCmdStartTX = 0x31,      // Switches to TX state and starts transmission of a packet.
        kCmdTXHop = 0x37,        // Hop to a new frequency while in TX.
        kCmdWriteTXFIFO = 0x66,  // Writes data byte(s) to the TX FIFO.

        // RX Commands
        kCmdPacketInfo =
            0x16,  // Returns information about the length of the variable field in the last packet received.
        kCmdGetModemStatus = 0x22,  // Returns the interrupt status of the Modem Interrupt Group.
        kCmdStartRX = 0x32,         // Switches to RX state and starts reception of a packet.
        kCmdRXHop = 0x36,           // Manually hop to a new frequency while in RX mode.
        kCmdReadRXFIFO = 0x77,      // Reads data byte(s) from the RX FIFO.

        // Advanced Commands
        kCmdGetADCReading = 0x14,  // Performs conversions using the Auxiliary ADC and returns the results.
        kCmdGetPHStatus = 0x21,    // Returns the interrupt status of the Packet Handler Interrupt Group.
        kCmdGetChipStatus = 0x23,  // Returns the interrupt status of the Chip Interrupt Group.
    };

    int SPIWriteReadBlocking(uint8_t* tx_buf, uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true);
    inline int SPIWriteBlocking(uint8_t* tx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(tx_buf, nullptr, len_bytes, end_transaction);
    }
    inline int SPIReadBlocking(uint8_t* rx_buf, uint16_t len_bytes = 0, bool end_transaction = true) {
        return SPIWriteReadBlocking(nullptr, rx_buf, len_bytes, end_transaction);
    }

    /**
     * Helper function that checks whether the radio has processed its previous command and is ready to receive another.
     */
    bool ClearToSend();
    bool SendCommand(Command cmd, uint8_t* param_buf = nullptr, uint16_t param_buf_len = 0,
                     bool block_until_complete = true);

    Si4362(Si4362Config config_in) : config_(config_in) {};
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