#include "si4362.hh"

#include "comms.hh"
#include "generated/radio_config_Si4362.h"
#include "hal.hh"
#include "unit_conversions.hh"

static const uint8_t kConfigDataArray[] = RADIO_CONFIGURATION_DATA_ARRAY;
static const uint8_t kPowerUpDataArray[] = {RF_POWER_UP};

// Full sync words, MSb is first received bit, LSb is last received bit.
// First 12 bits are used as an "any transitions" preamble, followed by a 4 Byte sync word.
static const uint64_t kUATADSBSyncWord = 0b1110'10101100'11011101'10100100'11100010;
static const uint64_t kUATGroundUplinkSyncWord = 0b0001'01010011'00100010'01011011'00011101;
static const uint16_t kUATSyncWordLenBits = 36;

// Sync words formatted for Si4362 registers. LSb of MSB is received first.
static constexpr uint8_t kUATADSBSyncBytes[3] = {0b10111011, 0b00100101, 0b01000111};
// Make sure that the values entered into WDS are correct.
static_assert(kUATADSBSyncBytes[0] == 0xBB);
static_assert(kUATADSBSyncBytes[1] == 0x25);
static_assert(kUATADSBSyncBytes[2] == 0x47);

static constexpr uint8_t kUATGroundUplinkSyncBytes[3] = {0b01000100, 0b11011010, 0b10111000};
// Make sure that the values entered into WDS are correct.
static_assert(kUATGroundUplinkSyncBytes[0] == 0x44);
static_assert(kUATGroundUplinkSyncBytes[1] == 0xDA);
static_assert(kUATGroundUplinkSyncBytes[2] == 0xB8);

// Define message lengths and amke sure they are Byte aligned.
static const uint16_t kUATADSBLongMessageLenBits = 272;
static const uint16_t kUATADSBLongMessageLenBytes = kUATADSBLongMessageLenBits / kBitsPerByte;
static_assert(kUATADSBLongMessageLenBytes * kBitsPerByte == kUATADSBLongMessageLenBits);
static const uint16_t kUATADSBShortMessageLenBits = 144;
static const uint16_t kUATADSBShortMessageLenBytes = kUATADSBShortMessageLenBits / kBitsPerByte;
static_assert(kUATADSBShortMessageLenBytes * kBitsPerByte == kUATADSBShortMessageLenBits);

// Basic ADS-B message RS parity is RS(30,18) code with 12 Bytes of parity capable of correcting up to 6 symbol errors
// per block.
// Long ADS-B message RS parity is RS(48, 34) code with 14 Bytes of parity capable of correcting up to 7 symbol errors
// per block.

void Si4362::ModemConfig::print() {
    printf("Si4362 Modem Configuration\r\n");
    printf("\tMODEM_DECIMATION_CFG1\r\n");
    printf("\t\tndec2=%u\r\n", ndec2);
    printf("\t\tndec1=%u\r\n", ndec1);
    printf("\t\tndec0=%u\r\n", ndec0);
    printf("\tMODEM_DECIMATION_CFG0\r\n");
    printf("\t\tdwn3byp=%u\r\n", dwn3byp);
    printf("\t\tdwn2byp=%u\r\n", dwn2byp);
    printf("\tMODEM_DECIMATION_CFG2\r\n");
    printf("\t\tndec3=%u\r\n", ndec3);
    printf("\t\tndec2gain=%u\r\n", ndec2gain);
    printf("\t\tndec2agc=%u\r\n", ndec2agc);
    printf("\tMODEM_BCR_OSR\r\n");
    printf("\t\trxosr=%u\r\n", rxosr);
    printf("\tMODEM_BCR_NCO_OFFSET\r\n");
    printf("\t\tncoff=%u\r\n", ncoff);
}

bool Si4362::Init(bool spi_already_initialized) {
    // Si4362 enable pin.
    gpio_init(config_.enable_pin);
    gpio_set_dir(config_.enable_pin, GPIO_OUT);
    SetEnable(true);  // Enable the Si4362.
    uint32_t enable_timestamp_ms = get_time_since_boot_ms();

    // Si4362 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 1);  // Deselect the Si4362.
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
    }

    // Send powerup command with no parameters, no pre-block on CTS, with post-block on CTS.
    if (!SendCommand(kCmdPowerUp, nullptr, 0, false, true)) {
        CONSOLE_ERROR("Si4362::Init", "Failed to power up the Si4362.");
        return false;
    }

    // Busy wait until bootup timeout has elapsed. Don't wait for CTS before (chip isn't powered on yet and won't
    // talk), but do wait for CTS after (chip replies to confirm power up).
    if (!SendCommand(static_cast<Command>(kPowerUpDataArray[0]), kPowerUpDataArray + 1, sizeof(kPowerUpDataArray) - 1,
                     false, true)) {
        CONSOLE_ERROR("Si4362::Init", "Failed to get CTS after waiting %lu ms.", kBootupDelayMs);
        return false;
    }

    // Send the generated data array from WDS.
    if (!SendDataArray(kConfigDataArray, sizeof(kConfigDataArray))) {
        CONSOLE_ERROR("Si4362::Init", "Failed to send configuration data.");
        return false;
    }

    // Override the data rate to 1.041667.
    ModemConfig modem_config = {};
    GetModemConfig(modem_config);
    // Original rxosr = 60;
    // 60*500 = rxosr*1041
    // rxosr = 60*500/1041 = 28.8
    modem_config.rxosr = 29;
    SetModemConfig(modem_config);

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

bool Si4362::SetDeviceState(DeviceState state, bool verify) {
    if (!SendCommand(kCmdChangeState, (uint8_t*)&state, sizeof(state))) {
        CONSOLE_ERROR("Si4362::SetDeviceState", "SendCommand failed while setting device state to %s.",
                      DeviceStateToString(state));
        return false;
    }
    if (!verify) {
        return true;
    }
    // Verify that the device state was set correctly.
    DeviceState verify_state = DeviceState::kStateInvalid;
    uint8_t channel = UINT8_MAX;
    if (!GetDeviceState(verify_state, channel)) {
        CONSOLE_ERROR("Si4362::SetDeviceState", "Failed to verify new device state; wanted %s but received %s.",
                      DeviceStateToString(state), DeviceStateToString(verify_state));
        return false;
    }
    return true;
}

bool Si4362::GetModemConfig(Si4362::ModemConfig& modem_config) {
    uint8_t data[kMaxNumPropertiesAtOnce] = {0};
    bool ret = true;

    // Get MODEM_DECIMATION_CFG1, MODEM_DECIMATION_CFG0
    ret &= GetProperty(kGroupModem, 3, 0x1e, data);

    // MODEM_DECIMATION_CFG1
    modem_config.ndec2 = data[0] >> 6;
    modem_config.ndec1 = (data[0] >> 4) & 0b11;
    modem_config.ndec0 = (data[0] >> 1) & 0b111;

    // MODEM_DECIMATION_CFG0
    modem_config.dwn3byp = (data[1] >> 5) & 0b1;
    modem_config.dwn2byp = (data[1] >> 4) & 0b1;

    // MODEM_DECIMATION_CFG2
    modem_config.ndec3 = (data[2] >> 5) & 0b11;
    modem_config.ndec2gain = (data[2] >> 3) & 0b11;
    modem_config.ndec2agc = (data[2] >> 2) & 0b1;

    // MODEM_BCR_OSR
    ret &= GetProperty(kGroupModem, 2, 0x22, data);
    modem_config.rxosr = ((data[0] & 0xF) << 8) | data[1];

    // MODEM_BCR_NCO_OFFSET
    ret &= GetProperty(kGroupModem, 3, 0x24, data);
    modem_config.ncoff = ((data[0] & 0xb111111) << 16) | (data[1] << 8) | data[2];

    return ret;
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

    // Block here to avoid spamming the Si4362 to death.
    while (get_time_since_boot_us() - last_cts_check_us_ < kCTSCheckIntervalUs) {
        // Wait for the CTS check interval to pass before checking CTS again.
    }
    last_cts_check_us_ = get_time_since_boot_us();

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

bool Si4362::SendCommand(Command cmd, const uint8_t* param_buf, uint16_t param_buf_len, bool pre_block_until_cts,
                         bool post_block_until_cts, bool end_transaction) {
    // Wait until CTS before sending a packet.
    if (pre_block_until_cts) {
        uint32_t begin_wait_timestamp_ms = get_time_since_boot_ms();
        while (!ClearToSend()) {
            // Wait for the Si4362 to process the command.
            if (get_time_since_boot_ms() - begin_wait_timestamp_ms > kSendCommandTimeoutMs) {
                CONSOLE_ERROR("Si4362::SendCommand", "Timed out after waiting %lu ms for CTS before sending command.",
                              kSendCommandTimeoutMs);
                return false;
            }
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

    // If post_block_until_cts is true, wait for the Si4362 to process the command and assert CTS.
    if (post_block_until_cts) {
        uint32_t begin_wait_timestamp_ms = get_time_since_boot_ms();
        while (!ClearToSend(end_transaction)) {
            // Wait for the Si4362 to process the command.
            if (get_time_since_boot_ms() - begin_wait_timestamp_ms > kSendCommandTimeoutMs) {
                CONSOLE_ERROR("Si4362::SendCommand", "Timed out after waiting %lu ms for CTS after sending command.",
                              kSendCommandTimeoutMs);
                return false;
            }
        }
    }
    return true;
}

bool Si4362::SendDataArray(const uint8_t* data, uint16_t len_bytes) {
    uint16_t data_array_line = 0;  // Keep track of the line number for debugging purposes.
    for (uint16_t index = 0; index < len_bytes;) {
        // num_bytes_to_send is the number of bytes to send in this sub-array, including the command byte.
        uint16_t num_bytes_to_send = data[index];
        if (num_bytes_to_send == 0) {
            return true;  // Exiting early, found 0 length subarray.
        } else if (num_bytes_to_send > len_bytes - index) {
            CONSOLE_ERROR("Si4362::SendDataArray", "Invalid data array length %d.", num_bytes_to_send);
            return false;
        }

        Command cmd = static_cast<Command>(data[index + 1]);
        if (!SendCommand(cmd, data + index + 2, num_bytes_to_send - 1)) {
            CONSOLE_ERROR("Si4362::SendDataArray", "Failed to send cmd=0x%X at data array line %d.", cmd,
                          data_array_line);
            return false;
        }
        index += num_bytes_to_send + 1;
        data_array_line++;
    }
    return true;
}

bool Si4362::SetModemConfig(const ModemConfig& modem_config) {
    bool ret = true;
    uint8_t data[kMaxNumPropertiesAtOnce] = {0};

    // MODEM_BCR_OSR
    data[0] = (modem_config.rxosr >> 8) & 0xF;
    data[1] = modem_config.rxosr & 0xFF;
    ret &= SetProperty(kGroupModem, 2, 0x22, data);

    return ret;
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
    // Block until receiving a CTS before and after the read command, and don't de-assert chip select in order to allow
    // clocking out the result in the same transaction.
    if (!SendCommand(cmd, command_buf, command_buf_len, true, true, false)) {
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