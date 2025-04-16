#include "si4362.hh"

#include "comms.hh"
#include "hal.hh"

static const uint32_t kBootupDelayMs = 10;
static const uint32_t kSendCommandTimeoutMs = 1000;

static const uint64_t kUATADSBSyncWord = 0b111010101100110111011010010011100010;
static const uint64_t kUATGroundUplinkSyncWord = 0b000101010011001000100101101100011101;
static const uint16_t kUATSyncWordLenBits = 36;
// Basic ADS-B message RS parity is RS(30,18) code with 12 Bytes of parity capable of correcting up to 6 symbol errors
// per block.

// Long ADS-B message RS parity is RS(48, 34) code with 14 Bytes of parity capable of correcting up to 7 symbol errors
// per block.

bool Si4362::Init(bool spi_already_initialized) {
    // Si4362 enable pin.
    gpio_init(config_.enable_pin);
    gpio_set_dir(config_.enable_pin, GPIO_OUT);
    SetEnable(true);  // Enable the Si4362.
    uint32_t enable_timestamp_ms = get_time_since_boot_ms();

    // Si4362 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // Si4362 IRQ pin.
    gpio_init(config_.irq_pin);
    gpio_set_dir(config_.irq_pin, GPIO_IN);
    gpio_set_pulls(config_.irq_pin, true, false);  // IRQ pin is pulled up.

    if (!spi_already_initialized) {
        // Si4362 SPI pins.
        gpio_set_function(config_.spi_clk_pin, GPIO_FUNC_SPI);
        gpio_set_function(config_.spi_mosi_pin, GPIO_FUNC_SPI);
        gpio_set_function(config_.spi_miso_pin, GPIO_FUNC_SPI);
        gpio_set_drive_strength(config_.spi_clk_pin, config_.spi_drive_strength);
        gpio_set_drive_strength(config_.spi_mosi_pin, config_.spi_drive_strength);
        gpio_set_drive_strength(config_.spi_cs_pin, config_.spi_drive_strength);
        gpio_set_pulls(config_.spi_clk_pin, config_.spi_pullup, config_.spi_pulldown);   // Clock pin pulls.
        gpio_set_pulls(config_.spi_mosi_pin, config_.spi_pullup, config_.spi_pulldown);  // MOSI pin pulls.
        gpio_set_pulls(config_.spi_cs_pin, config_.spi_pullup, config_.spi_pulldown);    // CS pin pulls.
        gpio_set_pulls(config_.spi_miso_pin, config_.spi_pullup, config_.spi_pulldown);  // MISO pin pulls.

        // Initialize SPI Peripheral.
        spi_init(config_.spi_handle, config_.spi_clk_freq_hz);
        spi_set_format(config_.spi_handle,
                       8,           // Bits per transfer.
                       SPI_CPOL_0,  // Polarity (CPOL).
                       SPI_CPHA_0,  // Phase (CPHA).
                       SPI_MSB_FIRST);
        active_clk_config_ = spi_get_clk();
        // Nobody else is on the bus yet, so we don't have to worry about restoring the standby clock config.
    } else {
        // SPI peripheral was already initialized. Make sure to not stomp on it when setting a clock rate.
        standby_clk_config_ = spi_get_clk();
        spi_set_baudrate(config_.spi_handle, config_.spi_clk_freq_hz);
        active_clk_config_ = spi_get_clk();
        spi_set_clk(standby_clk_config_);
    }

    while (get_time_since_boot_ms() - enable_timestamp_ms < kBootupDelayMs) {
        // Busy wait until bootup timeout has elapsed.
    }

    // Attempt to read the Si4362!
    if (!SendCommand(Command::kCmdPowerUp)) {
        CONSOLE_ERROR("Si4362::Init", "Failed to power up Si4362.");
        return false;
    }
    return true;
}

int Si4362::SPIWriteReadBlocking(uint8_t* tx_buf, uint8_t* rx_buf, uint16_t len_bytes, bool end_transaction) {
    int bytes_written = 0;

    standby_clk_config_ = spi_get_clk();  // Save existing clock config.
    spi_set_clk(active_clk_config_);

    gpio_put(config_.spi_cs_pin, false);

    if (tx_buf == nullptr) {
        // Transmit 0's when reading.
        bytes_written = spi_read_blocking(config_.spi_handle, 0x0, rx_buf, len_bytes);
    } else if (rx_buf == nullptr) {
        bytes_written = spi_write_blocking(config_.spi_handle, tx_buf, len_bytes);
    } else {
        bytes_written = spi_write_read_blocking(config_.spi_handle, tx_buf, rx_buf, len_bytes);
    }

    if (bytes_written < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWriteReadBlocking", "SPI write read call returned error code 0x%x.",
                      bytes_written);
    }
    if (end_transaction) {
        gpio_put(config_.spi_cs_pin, true);
    }

    spi_set_clk(standby_clk_config_);  // Restore clock config.
    return bytes_written;
}

bool Si4362::ClearToSend(bool end_transaction) {
    // Truth table
    // end_transaction | CTS | Chip Select at end of Transaction
    // ----------------|-----|----------------------------------
    // true            | 1   | 1
    // true            | 0   | 1
    // false           | 1   | 0
    // false           | 0   | 1

    // Don't use SendCommand() here since this is called by SendCommand() and we don't want a circular recursion loop.
    uint8_t tx_buf[2] = {
        Command::kCmdReadCmdBuff,
        0x0,
    };
    uint8_t rx_buf[2] = {0};

    int ret = SPIWriteReadBlocking(tx_buf, rx_buf, sizeof(tx_buf), end_transaction);
    if (ret < 0) {
        CONSOLE_ERROR("Si4362::ClearToSend", "Failed to read command buffer.");
        return false;
    } else if (ret < sizeof(tx_buf)) {
        CONSOLE_ERROR("Si4362::ClearToSend", "Failed to read command buffer, only %d bytes written.", ret);
        return false;
    }
    if (rx_buf[1] == 0xFF) {
        // CTS == 1
        return true;
    } else {
        // CTS == 0
        gpio_put(config_.spi_cs_pin,
                 true);  // Didn't want to end the transaction, but not Clear to Send; end it anyways.
        return false;
    }
}

bool Si4362::GetProperty(Group group, uint8_t num_props, uint8_t start_prop, uint8_t* data) {
    if (num_props > kMaxNumPropertiesAtOnce) {
        CONSOLE_ERROR("Si4362::GetProperty", "Tried to get %d properties at once, max is %d.", num_props,
                      kMaxNumPropertiesAtOnce);
        return false;
    }

    // Get the properties from the Si4362.
    uint8_t params_buf[3] = {group, num_props, start_prop};
    if (!ReadCommand(kCmdGetProperty, data, num_props, params_buf, sizeof(params_buf))) {
        CONSOLE_ERROR("Si4362::GetProperty", "Failed to send get property command.");
        return false;
    }
    return true;
}

bool Si4362::SendCommand(Command cmd, uint8_t* param_buf, uint16_t param_buf_len, bool block_until_cts,
                         bool end_transaction) {
    // Wait until CTS before sending a packet.
    uint32_t begin_wait_timestamp_ms = get_time_since_boot_ms();
    while (!ClearToSend()) {
        // Wait for the Si4362 to process the command.
        if (get_time_since_boot_ms() - begin_wait_timestamp_ms > kSendCommandTimeoutMs) {
            CONSOLE_ERROR("Si4362::SendCommand", "Timed out after waiting %lu ms for command to complete.",
                          kSendCommandTimeoutMs);
            return false;
        }
    }

    uint8_t tx_buf[sizeof(cmd) + param_buf_len];
    tx_buf[0] = cmd;
    memcpy(tx_buf + sizeof(cmd), param_buf, param_buf_len);

    int ret = SPIWriteBlocking(tx_buf, sizeof(tx_buf), true);
    if (ret < 0) {
        CONSOLE_ERROR("Si4362::SendCommand", "Failed to send command with error code 0x%lx.", ret);
        return false;
    } else if (ret < sizeof(tx_buf)) {
        CONSOLE_ERROR("Si4362::SendCommand", "Failed to send command, only %d bytes written.", ret);
        return false;
    }

    // If block_until_cts is true, wait for the Si4362 to process the command and assert CTS.
    begin_wait_timestamp_ms = get_time_since_boot_ms();
    if (block_until_cts) {
        while (!ClearToSend(end_transaction)) {
            // Wait for the Si4362 to process the command.
            if (get_time_since_boot_ms() - begin_wait_timestamp_ms > kSendCommandTimeoutMs) {
                CONSOLE_ERROR("Si4362::SendCommand", "Timed out after waiting %lu ms for command to complete.",
                              kSendCommandTimeoutMs);
                return false;
            }
        }
    }
    return true;
}

bool Si4362::SetProperty(Group group, uint8_t num_props, uint8_t start_prop, uint8_t* data) {
    if (num_props > kMaxNumPropertiesAtOnce) {
        CONSOLE_ERROR("Si4362::SetProperty", "Tried to set %d properties at once, max is %d.", num_props,
                      kMaxNumPropertiesAtOnce);
        return false;
    }

    // Set the properties on the Si4362.
    uint8_t params_buf[3 + num_props] = {0};
    params_buf[0] = group;
    params_buf[1] = num_props;
    params_buf[2] = start_prop;
    memcpy(params_buf + 3, data, num_props);

    if (!SendCommand(kCmdSetProperty, params_buf, sizeof(params_buf))) {
        CONSOLE_ERROR("Si4362::SetProperty", "Failed to send set property command.");
        return false;
    }
    return true;
}

bool Si4362::ReadCommand(Command cmd, uint8_t* response_buf, uint16_t response_buf_len, uint8_t* command_buf,
                         uint16_t command_buf_len) {
    // Send the read command and wait for a CTS signal to read the result.
    // Block until receiving a CTS, and don't de-assert chip select in order to allow clocking out the result in the
    // same transaction.
    if (!SendCommand(cmd, command_buf, command_buf_len, true, false)) {
        CONSOLE_ERROR("Si4362::ReadCommand", "Failed to send read command.");
        return false;
    }
    // Read the response.
    int ret = SPIReadBlocking(response_buf, response_buf_len, true);
    if (ret < 0) {
        CONSOLE_ERROR("Si4362::ReadCommand", "Failed to read command buffer with error code 0x%lx.", ret);
        return false;
    } else if (ret < response_buf_len) {
        CONSOLE_ERROR("Si4362::ReadCommand", "Failed to read command buffer, only %d bytes read.", ret);
        return false;
    }
    return true;
}