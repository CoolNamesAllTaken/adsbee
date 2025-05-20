#include "cc1312.hh"

#include "comms.hh"

const CC1312::SPIPeripheralConfig kDefaultSPIPeripheralConfig;  // use defaults
const CC1312::SPIPeripheralConfig kBootloaderSPIPeripheralConfig = {
    .bits_per_transfer = 8,
    .cpol = SPI_CPOL_1,
    .cpha = SPI_CPHA_1,
    .order = SPI_MSB_FIRST,
};

const uint32_t kSPITransactionTImeoutMs = 100;  // Timeout for SPI transactions.

bool CC1312::Init(bool spi_already_initialized) {
    // CC1312 enable pin.
    gpio_init(config_.enable_pin);
    gpio_set_dir(config_.enable_pin, GPIO_OUT);
    SetEnable(true);  // Enable the CC1312.
    uint32_t enable_timestamp_ms = get_time_since_boot_ms();

    // CC1312 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 1);  // Deselect the CC1312.
    // CC1312 IRQ pin.
    gpio_init(config_.irq_pin);
    gpio_set_dir(config_.irq_pin, GPIO_IN);
    gpio_set_pulls(config_.irq_pin, true, false);  // IRQ pin is pulled up.

    if (!spi_already_initialized) {
        // CC1312 SPI pins.
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

    return true;
}

CC1312::CommandReturnStatus CC1312::BootloaderCommandGetStatus() {
    uint8_t cmd_buf[1] = {kCmdGetStatus};
    if (!BootloaderSendBuffer(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandGetStatus", "Failed to send command.");
        return kCmdRetDriverError;
    }
    uint8_t status_buf[1] = {0};
    if (!BootloaderReceiveBuffer(status_buf, sizeof(status_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandGetStatus", "Failed to receive command status.");
        return kCmdRetDriverError;
    }
    CommandReturnStatus return_status = static_cast<CommandReturnStatus>(status_buf[0]);
    if (return_status != kCmdRetSuccess) {
        CONSOLE_ERROR("CC1312::BootloaderCommandGetStatus", "Command failed with status 0x%x. (%s).", return_status,
                      CommandReturnStatusToString(return_status));
        return return_status;
    }

    return return_status;
}

bool CC1312::BootloaderCommandMemoryRead(uint32_t address, uint32_t* buf, uint8_t buf_len, bool is_32bit) {
    if ((is_32bit && buf_len > 63) || (is_32bit && buf_len > 253)) {
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
            buf[i] = (data_buf[4 * i] << 24) | (data_buf[4 * i + 1] << 16) | (data_buf[4 * i + 2] << 8) |
                     data_buf[4 * i + 3];
        }
    } else {
        for (uint8_t i = 0; i < buf_len; i++) {
            buf[i] = data_buf[i];
        }
    }
    return true;
}

bool CC1312::BootloaderCommandPing() {
    uint8_t cmd_buf[1] = {kCmdPing};
    bool ping_acked = BootloaderSendBufferCheckSuccess(cmd_buf, sizeof(cmd_buf));
    if (!ping_acked) {
        CONSOLE_ERROR("CC1312::BootloaderCommandPing", "Ping command failed.");
        return false;
    }
    return true;
}

bool CC1312::BootloaderCommandReset() {
    uint8_t cmd_buf[1] = {kCmdReset};
    bool reset_acked = BootloaderSendBuffer(cmd_buf, sizeof(cmd_buf));
    if (!reset_acked) {
        CONSOLE_ERROR("CC1312::BootloaderCommandReset", "Reset command failed.");
        return false;
    }
    return true;
}

bool CC1312::BootloaderReadCCFGConfig(BootloaderCCFGConfig& ccfg_config) { return true; }

bool CC1312::BootloaderReceiveBuffer(uint8_t* buf, uint16_t buf_len_bytes) {
    uint8_t rx_buf[buf_len_bytes + 2] = {0};  // Includes size Byte and checksum Byte.
    uint32_t start_time_ms = get_time_since_boot_ms();
    bool received_response = false;
    while (!received_response) {
        if (get_time_since_boot_ms() - start_time_ms > kSPITransactionTImeoutMs) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer", "Timed out waiting for response from CC1312.");
            return false;
        }

        // Read the first byte of the response.
        int16_t bytes_read = SPIReadBlocking(rx_buf, 1, false);
        if (bytes_read < 0) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer",
                          "Failed to read response, SPI write read call returned error code 0x%x.", bytes_read);
            return false;
        } else if (bytes_read != 1) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer",
                          "Failed to read first Byte of response, expected %d Bytes but read %d.", 1, bytes_read);
            return false;
        } else if (rx_buf[0] != 0) {
            received_response = true;
        }
    }

    uint16_t rx_len_bytes = rx_buf[0];
    uint8_t calculated_checksum = 0;

    int16_t bytes_read =
        SPIReadBlocking(rx_buf + 1, rx_len_bytes - 1, false);  // End transaction after reading the buffer.
    bool read_success = true;
    if (bytes_read < 0) {
        CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer",
                      "Failed to read response, SPI write read call returned error code 0x%x.", bytes_read);
        read_success = false;
    } else if (bytes_read != rx_len_bytes - 1) {
        CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer", "Failed to read response, expected %d Bytes but read %d.",
                      rx_len_bytes - 1, bytes_read);
        read_success = false;
    } else {
        // Verify received checksum.
        uint16_t received_checksum = rx_buf[1];
        for (uint16_t i = 2; i < rx_len_bytes; i++) {
            calculated_checksum += rx_buf[i];
        }
        if (calculated_checksum != received_checksum) {
            CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer", "Checksum mismatch, expected 0x%x but got 0x%x.",
                          received_checksum, calculated_checksum);
            read_success = false;
        }
    }
    uint8_t ack_nack_byte = read_success ? ProtocolByte::kProtocolByteAck : ProtocolByte::kProtocolByteNack;
    SPIWriteBlocking(&ack_nack_byte, 1, true);  // Send ACK or NACK back to the CC1312, then end the transaction.
    if (!read_success) {
        return false;
    }

    // Copy the buffer to the output buffer.
    if (buf_len_bytes < rx_len_bytes - 2) {
        CONSOLE_ERROR("CC1312::BootloaderReceiveBuffer", "Buffer too small, expected %d bytes but got %d.",
                      buf_len_bytes, rx_len_bytes - 2);
        return false;
    }
    memcpy(buf, rx_buf + 2, rx_len_bytes - 2);  // Copy the buffer to the output buffer.
    return true;
}

bool CC1312::BootloaderSendBuffer(uint8_t* buf, uint16_t buf_len_bytes) {
    // Prepare the buffer to send.
    // Send packet size is (buf_len_bytes + size Byte + checksum Byte).
    uint8_t tx_len_bytes = buf_len_bytes + 2;
    uint8_t checksum = 0;
    for (uint16_t i = 0; i < buf_len_bytes; i++) {
        checksum += buf[i];
    }
    uint8_t tx_buf[tx_len_bytes] = {0};
    tx_buf[0] = tx_len_bytes;
    tx_buf[1] = checksum;
    memcpy(tx_buf + 2, buf, buf_len_bytes);
    uint32_t start_time_ms = get_time_since_boot_ms();

    // Send the buffer.
    int16_t bytes_written =
        SPIWriteBlocking(tx_buf, tx_len_bytes,
                         false);  // Don't end transaction, keep reading till we get a nonzero response.
    if (bytes_written < 0) {
        SPIEndTransaction();  // End transaction after error.
        CONSOLE_ERROR("CC1312::BootloaderSendBuffer",
                      "Failed to send buffer, SPI write read call returned error code 0x%x.", bytes_written);
        return false;
    } else if (bytes_written < tx_len_bytes) {
        SPIEndTransaction();  // End transaction after error.
        CONSOLE_ERROR("CC1312::BootloaderSendBuffer", "Failed to send buffer, only %d bytes written.", bytes_written);
        return false;
    }

    // Wait for a response.
    bool got_response = false;
    uint8_t rx_byte;
    while (!got_response) {
        if (get_time_since_boot_ms() - start_time_ms > kSPITransactionTImeoutMs) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderSendBuffer", "Timed out waiting for response from CC1312.");
            return false;
        }

        rx_byte = 0;
        int16_t bytes_read = SPIReadBlocking(&rx_byte, 1, false);
        if (bytes_read < 0) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderSendBuffer",
                          "Failed to read response, SPI write read call returned error code 0x%x.", bytes_read);
            return false;
        } else if (bytes_read != 1) {
            SPIEndTransaction();  // End transaction after error.
            CONSOLE_ERROR("CC1312::BootloaderSendBuffer", "Failed to read response, only %d Bytes read.", bytes_read);
            return false;
        } else if (rx_byte != 0) {
            got_response = true;
            SPIEndTransaction();  // End the transaction after receiving a response.
        }
    }

    // Interpret the response.
    if (rx_byte == ProtocolByte::kProtocolByteNack) {
        CONSOLE_ERROR("CC1312::BootloaderSendBuffer", "Received NACK from CC1312.");
        return false;
    } else if (rx_byte != kProtocolByteAck) {
        CONSOLE_ERROR("CC1312::BootloaderSendBuffer", "Received unknown response from CC1312: 0x%x.", rx_byte);
        return false;
    }
    return true;
}

bool CC1312::BootloaderSendBufferCheckSuccess(uint8_t* buf, uint16_t buf_len_bytes) {
    if (!BootloaderSendBuffer(buf, buf_len_bytes)) {
        CONSOLE_ERROR("CC1312::BootloaderSendBufferCheckSuccess", "Failed to send command.");
        return false;
    }
    if (BootloaderCommandGetStatus() != kCmdRetSuccess) {
        CONSOLE_ERROR("CC1312::BootloaderSendBufferCheckSuccess", "Command was sent but was unsuccessful.");
        return false;
    }
    return true;
}

bool CC1312::EnterBootloader() {
    SetEnable(false);
    gpio_put(config_.sync_pin, 1);
    SetEnable(true);
    in_bootloader_ = true;
    sleep_ms(kBootupDelayMs);  // Wait for the CC1312 to boot up.

    return BootloaderCommandPing();
}

bool CC1312::ExitBootloader() {
    in_bootloader_ = false;
    SetEnable(false);
    gpio_put(config_.sync_pin, 0);
    SetEnable(true);

    return true;
}

void CC1312::SPIBeginTransaction() {
    if (in_bootloader_) {
        // Bootlaoder is active, override CPHA and CPOL.
        spi_set_format(config_.spi_handle, kBootloaderSPIPeripheralConfig.bits_per_transfer,
                       kBootloaderSPIPeripheralConfig.cpol, kBootloaderSPIPeripheralConfig.cpha,
                       kBootloaderSPIPeripheralConfig.order);
    }
    standby_clk_config_ = spi_get_clk();  // Save existing clock config.
    spi_set_clk(active_clk_config_);

    gpio_put(config_.spi_cs_pin, false);
}

void CC1312::SPIEndTransaction() {
    gpio_put(config_.spi_cs_pin, true);

    spi_set_clk(standby_clk_config_);  // Restore clock config.
    if (in_bootloader_) {
        // Bootlaoder is active, restore CPHA and CPOL.
        spi_set_format(config_.spi_handle, kDefaultSPIPeripheralConfig.bits_per_transfer,
                       kDefaultSPIPeripheralConfig.cpol, kDefaultSPIPeripheralConfig.cpha,
                       kDefaultSPIPeripheralConfig.order);
    }
}

int CC1312::SPIWriteReadBlocking(uint8_t* tx_buf, uint8_t* rx_buf, uint16_t len_bytes, bool end_transaction) {
    int bytes_written = 0;

    SPIBeginTransaction();

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
        SPIEndTransaction();
    }
    return bytes_written;
}