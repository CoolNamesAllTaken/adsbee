#include "cc1312.hh"

// Get access to raw application binary for flashing.
#include "bin/binaries.c"
#include "crc.hh"  // For IEEE 802.3 CRC32 calculation.
#include "hal.hh"

const CC1312::SPIPeripheralConfig kDefaultSPIPeripheralConfig;  // use defaults
const CC1312::SPIPeripheralConfig kBootloaderSPIPeripheralConfig = {
    .bits_per_transfer = 8,
    .cpol = SPI_CPOL_1,
    .cpha = SPI_CPHA_1,
    .order = SPI_MSB_FIRST,
};

bool CC1312::Init(bool spi_already_initialized) {
    // CC1312 enable pin.
    gpio_init(config_.enable_pin);
    SetEnable(SettingsManager::kEnableStateEnabled);  // Enable the CC1312.
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

    // TODO: Attempt communication before entering the bootloader.
    CONSOLE_ERROR("CC1312::Init", "Unable to communicate with CC1312. Entering bootloader mode.");
    if (!EnterBootloader() || !BootloaderCommandPing()) {
        CONSOLE_ERROR("CC1312::Init", "Failed to enter bootloader mode.");
        return false;
    }
    CONSOLE_INFO("CC1312::Init", "Applying default bootloader CCFG configuration to CC1312.");
    if (!BootloaderWriteCCFGConfig(config_.ccfg_config)) {
        CONSOLE_ERROR("CC1312::Init", "Failed to write default bootloader CCFG configuration.");
        return false;
    }
    // TODO: Attempt to flash firmware to the CC1312.
    CONSOLE_INFO("CC1312::Init", "Exiting bootloader mode.");
    if (!ExitBootloader()) {
        CONSOLE_ERROR("CC1312::Init", "Failed to exit bootloader mode.");
        return false;
    }

    // TODO: Check that the CC1312 can be communicated with successfully.
    CONSOLE_INFO("CC1312::Init", "CC1312 initialized successfully.");

    return true;
}

bool CC1312::BootloaderCommandBankErase() {
    uint8_t cmd_buf[1] = {kCmdBankErase};
    if (!BootloaderSendBufferCheckSuccess(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandBankErase", "Failed to send bank erase command.");
        return false;
    }
    return true;
}

bool CC1312::BootloaderCommandCRC32(uint32_t& crc, uint32_t address, uint32_t num_bytes, uint32_t read_repeat_count) {
    uint8_t cmd_buf[13] = {kCmdCRC32,
                           static_cast<uint8_t>((address >> 24) & 0xFFu),
                           static_cast<uint8_t>((address >> 16) & 0xFFu),
                           static_cast<uint8_t>((address >> 8) & 0xFFu),
                           static_cast<uint8_t>(address & 0xFFu),
                           static_cast<uint8_t>((num_bytes >> 24) & 0xFFu),
                           static_cast<uint8_t>((num_bytes >> 16) & 0xFFu),
                           static_cast<uint8_t>((num_bytes >> 8) & 0xFFu),
                           static_cast<uint8_t>(num_bytes & 0xFFu),
                           static_cast<uint8_t>((read_repeat_count >> 24) & 0xFFu),
                           static_cast<uint8_t>((read_repeat_count >> 16) & 0xFFu),
                           static_cast<uint8_t>((read_repeat_count >> 8) & 0xFFu),
                           static_cast<uint8_t>(read_repeat_count & 0xFFu)};
    if (!BootloaderSendBuffer(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandCRC32", "Failed to send CRC32 command.");
        return false;
    }
    uint8_t crc_buf[4] = {0};
    if (!BootloaderReceiveBuffer(crc_buf, sizeof(crc_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandCRC32", "Failed to receive CRC32 result.");
        return false;
    }
    crc = (static_cast<uint32_t>(crc_buf[0]) << 24) | (static_cast<uint32_t>(crc_buf[1]) << 16) |
          (static_cast<uint32_t>(crc_buf[2]) << 8) | static_cast<uint32_t>(crc_buf[3]);
    return true;
}

bool CC1312::BootloaderCommandDownload(uint32_t address, uint32_t num_bytes) {
    uint8_t cmd_buf[9]{kCmdDownload,
                       static_cast<uint8_t>((address >> 24) & 0xFFu),
                       static_cast<uint8_t>((address >> 16) & 0xFFu),
                       static_cast<uint8_t>((address >> 8) & 0xFFu),
                       static_cast<uint8_t>(address & 0xFFu),
                       static_cast<uint8_t>((num_bytes >> 24) & 0xFFu),
                       static_cast<uint8_t>((num_bytes >> 16) & 0xFFu),
                       static_cast<uint8_t>((num_bytes >> 8) & 0xFFu),
                       static_cast<uint8_t>(num_bytes & 0xFFu)};
    if (!BootloaderSendBufferCheckSuccess(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandDownload",
                      "Failed to send download command. Firmware size or address might be invalid, or something else "
                      "went wrong.");
        return false;
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

bool CC1312::BootloaderCommandSendData(const uint8_t* data, uint32_t data_len) {
    static const uint32_t kMaxDataLength = 255 - 3;  // Max packet length minus command, size, checksum Bytes.
    if (data_len > kMaxDataLength) {
        CONSOLE_ERROR("CC1312::BootloaderCommandSendData", "Data length %d exceeds maximum allowed length of %d bytes.",
                      data_len, kMaxDataLength);
        return false;
    }
    uint8_t cmd_buf[1 + data_len] = {0x0};
    cmd_buf[0] = kCmdSendData;
    memcpy(cmd_buf + 1, data, data_len);  // Copy the data to the command buffer.
    if (!BootloaderSendBufferCheckSuccess(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandSendData", "Programming failed.");
        return false;
    }
    return true;
}

bool CC1312::BootloaderCommandSetCCFG(BootloaderCCFGFieldID field_id, uint32_t value) {
    uint8_t cmd_buf[9] = {kCmdSetCCFG,
                          static_cast<uint8_t>((field_id >> 24) & 0xFFu),
                          static_cast<uint8_t>((field_id >> 16) & 0xFFu),
                          static_cast<uint8_t>((field_id >> 8) & 0xFFu),
                          static_cast<uint8_t>(field_id & 0xFFu),
                          static_cast<uint8_t>((value >> 24) & 0xFFu),
                          static_cast<uint8_t>((value >> 16) & 0xFFu),
                          static_cast<uint8_t>((value >> 8) & 0xFFu),
                          static_cast<uint8_t>(value & 0xFFu)};

    if (!BootloaderSendBufferCheckSuccess(cmd_buf, sizeof(cmd_buf))) {
        CONSOLE_ERROR("CC1312::BootloaderCommandSetCCFG", "Failed to send CCFG set command.");
        return false;
    }
    return true;
}

bool CC1312::BootloaderReadCCFGConfig(BootloaderCCFGConfig& ccfg_config) {
    uint32_t bl_config = 0;

    if (!BootloaderCommandMemoryRead(kBaseAddrCCFG + kCCFGRegOffBLConfig, &bl_config, 1)) {
        CONSOLE_ERROR("CC1312::BootloaderReadCCFGConfig", "Failed to read CCFG configuration.");
        return false;
    }

    ccfg_config.bl_enabled = ((bl_config >> 24) & 0xFF) == 0xC5;
    ccfg_config.bl_backdoor_level = (bl_config >> 16) & 0x01;       // Bit[16] is the backdoor level.
    ccfg_config.bl_backdoor_pin = (bl_config >> 8) & 0xFF;          // Bits[15:8] are the backdoor pin.
    ccfg_config.bl_backdoor_enabled = (bl_config & 0x0FF) == 0xC5;  // Bits[7:0] are the backdoor enabled flag.

    uint32_t erase_conf = 0;
    if (!BootloaderCommandMemoryRead(kBaseAddrCCFG + kCCFGRegOffEraseConf, &erase_conf, 1)) {
        CONSOLE_ERROR("CC1312::BootloaderReadCCFGConfig", "Failed to read CCFG erase configuration.");
        return false;
    }

    ccfg_config.chip_erase_disabled = ((erase_conf >> 8) & 0b1) == 0;  // Bit[8] is the chip erase disabled flag.
    ccfg_config.bank_erase_disabled = (erase_conf & 0b1) == 0;         // Bit[0] is the bank erase disabled flag.

    return true;
}

bool CC1312::BootloaderWriteCCFGConfig(const BootloaderCCFGConfig& ccfg_config) {
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDIDBankEraseDis, ccfg_config.bank_erase_disabled ? 0 : 1)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set bank erase disabled CCFG field.");
        return false;
    }
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDChipEraseDis, ccfg_config.chip_erase_disabled ? 0 : 1)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set chip erase disabled CCFG field.");
        return false;
    }
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDBLBackdoorEn, ccfg_config.bl_backdoor_enabled ? 0xC5 : 0xFF)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set bootloader backdoor enabled CCFG field.");
        return false;
    }
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDBLBackdoorPin, ccfg_config.bl_backdoor_pin)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set bootloader backdoor pin CCFG field.");
        return false;
    }
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDBackdoorLevel, ccfg_config.bl_backdoor_level ? 1 : 0)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set bootloader backdoor level CCFG field.");
        return false;
    }
    if (!BootloaderCommandSetCCFG(kCCFGFieldIDBLEnable, ccfg_config.bl_enabled ? 0xC5 : 0xFF)) {
        CONSOLE_ERROR("CC1312::BootloaderWriteCCFGConfig", "Failed to set bootloader enabled CCFG field.");
        return false;
    }

    return true;
}

bool CC1312::EnterBootloader() {
    SetEnable(SettingsManager::kEnableStateDisabled);
    gpio_put(config_.sync_pin, 1);
    SetEnable(SettingsManager::kEnableStateEnabled);
    in_bootloader_ = true;
    sleep_ms(kBootupDelayMs);  // Wait for the CC1312 to boot up.

    return BootloaderCommandPing();
}

bool CC1312::ExitBootloader() {
    in_bootloader_ = false;
    SetEnable(SettingsManager::kEnableStateDisabled);
    gpio_put(config_.sync_pin, 0);
    SetEnable(SettingsManager::kEnableStateEnabled);

    return true;
}

bool CC1312::BootloaderReceiveBuffer(uint8_t* buf, uint16_t buf_len_bytes) {
    uint8_t rx_buf[buf_len_bytes + 2] = {0};  // Includes size Byte and checksum Byte.
    uint32_t start_time_ms = get_time_since_boot_ms();
    bool received_response = false;
    while (!received_response) {
        if (get_time_since_boot_ms() - start_time_ms > kSPITransactionTimeoutMs) {
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
        if (get_time_since_boot_ms() - start_time_ms > kSPITransactionTimeoutMs) {
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

bool CC1312::Flash() {
    CONSOLE_PRINTF("CC1312::Flash: Entering bootloader.\r\n");
    if (!EnterBootloader()) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to enter bootloader mode.");
        return false;
    }

    // Erase the chip.
    CONSOLE_PRINTF("CC1312::Flash: Beginning flash erase.\r\n");
    if (!BootloaderCommandBankErase()) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to erase the chip.");
        return false;
    }
    CONSOLE_PRINTF("CC1312::Flash: Flash erase complete.\r\n");
    // Re-write the CCFG configuration.
    CONSOLE_PRINTF("CC1312::Flash: Writing CCFG configuration.\r\n");
    if (!BootloaderWriteCCFGConfig(config_.ccfg_config)) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to write CCFG configuration.");
        return false;
    }
    CONSOLE_PRINTF("CC1312::Flash: Verifying CCFG configuration.\r\n");
    BootloaderCCFGConfig ccfg_config;
    if (!BootloaderReadCCFGConfig(ccfg_config)) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to read CCFG configuration.");
        return false;
    }
    char ccfg_config_str[256];
    ccfg_config.print_to_buffer(ccfg_config_str, sizeof(ccfg_config_str));
    CONSOLE_PRINTF("CC1312::Flash: CCFG configuration read:\r\n%s", ccfg_config_str);
    if (ccfg_config != config_.ccfg_config) {
        char expected_ccfg_config_str[256];
        config_.ccfg_config.print_to_buffer(expected_ccfg_config_str, sizeof(expected_ccfg_config_str));
        CONSOLE_ERROR("CC1312::Flash",
                      "CCFG configuration does not match expected values after writing. Expected:\r\n%s, "
                      "Got:\r\n%s",
                      expected_ccfg_config_str, ccfg_config_str);
        return false;
    }
    CONSOLE_PRINTF("CC1312::Flash: CCFG configuration written and verified successfully.\r\n");

    CONSOLE_PRINTF("CC1312::Flash: Beginning flash programming. Application is %d Bytes\r\n", sub_ghz_radio_bin_size);

    // Send the download command.
    if (!BootloaderCommandDownload(kBaseAddrFlashMem, sub_ghz_radio_bin_size)) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to send download command.");
        return false;
    }
    CONSOLE_PRINTF("CC1312::Flash: Download command sent successfully.\r\n");

    // Send the application binary data.
    uint32_t flash_offset = 0;
    uint32_t num_chunks = sub_ghz_radio_bin_size / kBootloaderCommandSendDataMaxLenBytes +
                          (sub_ghz_radio_bin_size % kBootloaderCommandSendDataMaxLenBytes != 0 ? 1 : 0);
    uint32_t current_chunk = 0;
    while (flash_offset < sub_ghz_radio_bin_size) {
        uint32_t bytes_to_send = MIN(sub_ghz_radio_bin_size - flash_offset, kBootloaderCommandSendDataMaxLenBytes);
        if (!BootloaderCommandSendData(sub_ghz_radio_bin + flash_offset, bytes_to_send)) {
            CONSOLE_ERROR("CC1312::Flash", "Failed to send application data at offset %d.", flash_offset);
            // TODO: Attempt a retry here?
            return false;
        }
        flash_offset += bytes_to_send;
        current_chunk++;
        CONSOLE_PRINTF("CC1312::Flash: Sent %d Bytes, total sent: %d Bytes [%d / %d chunks].\r\n", bytes_to_send,
                       flash_offset, current_chunk, num_chunks);
    }
    CONSOLE_PRINTF("CC1312::Flash: Application data sent successfully.\r\n");

    // Verify application binary.
    uint32_t table_crc = crc32_ieee_802_3(sub_ghz_radio_bin, sub_ghz_radio_bin_size);
    uint32_t device_crc = 0;
    if (!BootloaderCommandCRC32(device_crc, kBaseAddrFlashMem, sub_ghz_radio_bin_size)) {
        CONSOLE_ERROR("CC1312::Flash", "Failed to calculate CRC32 of the application binary.");
        return false;
    }
    if (table_crc != device_crc) {
        CONSOLE_ERROR("CC1312::Flash", "CRC32 mismatch after flashing application binary. Expected 0x%x, got 0x%x.",
                      table_crc, device_crc);
        return false;
    }
    CONSOLE_PRINTF("CC1312::Flash: Application binary flashed successfully, CRC32 matches: 0x%x.\r\n", table_crc);

    // TODO: Prepare CC1312 to run the application binary.

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