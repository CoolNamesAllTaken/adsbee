#include "esp32.hh"

#include "hal.hh"

ESP32::ESP32(ESP32Config config_in) : config_(config_in) {}

bool ESP32::Init() {
    // ESP32 enable pin.
    gpio_init(config_.enable_pin);
    gpio_set_dir(config_.enable_pin, GPIO_OUT);
    SetEnable(true);
    // ESP32 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // ESP32 handshake pin.
    gpio_init(config_.spi_handshake_pin);
    gpio_set_dir(config_.spi_handshake_pin, GPIO_IN);
    gpio_set_pulls(config_.spi_handshake_pin, true,
                   false);  // Handshake pin is pulled up to not enter bootloader on startup.
    // Handshake line being pulled up results in false positive handshakes during startup, but this only happens during
    // bootup.

    // Require SPI pins to be initialized before this function is called, since they get shared.
    gpio_set_drive_strength(config_.spi_cs_pin, config_.spi_drive_strength);
    gpio_set_pulls(config_.spi_cs_pin, config_.spi_pullup, config_.spi_pulldown);  // CS pin pulls.

    // Delay for kBootupDelayMs to avoid a bunch of failed transactions while the ESP32 wakes up.
    uint32_t boot_start_timestamp_ms = get_time_since_boot_ms();
    while (get_time_since_boot_ms() - boot_start_timestamp_ms < kBootupDelayMs) {
    }

    return true;
}

bool ESP32::DeInit() {
    // ESP32 enable pin.
    SetEnable(false);
    return true;
}

bool ESP32::Update() {
    // IsEnabled() check happens at the higher level Update() function in SPICoprocessor, so don't repeat it here.

    uint32_t timestamp_ms = get_time_since_boot_ms();

    if (timestamp_ms - last_device_status_update_timestamp_ms_ > device_status_update_interval_ms) {
        // Query ESP32's device status.
        ObjectDictionary::ESP32DeviceStatus device_status;
        if (esp32.Read(ObjectDictionary::Address::kAddrDeviceStatus, device_status)) {
            last_device_status_update_timestamp_ms_ = timestamp_ms;
        } else {
            CONSOLE_ERROR("ESP32::Update", "Unable to read ESP32 status.");
            return false;
        }

        if (device_status.num_queued_sc_command_requests > 0) {
            uint16_t num_requests_processed = 0;
            while (num_requests_processed < device_status.num_queued_sc_command_requests &&
                   num_requests_processed < kMaxNumSCCommandRequestsPerUpdate) {
                // Read SCCommand request from ESP32.
                ObjectDictionary::SCCommandRequest sc_command_request;
                if (!esp32.Read(ObjectDictionary::Address::kAddrSCCommandRequests, sc_command_request)) {
                    CONSOLE_ERROR("ESP32::Update", "Unable to read SCCommand request %d/%d from ESP32.",
                                  num_requests_processed + 1, device_status.num_queued_sc_command_requests);
                    return false;
                }
                // Execute the request.
                if (!ExecuteSCCommandRequest(sc_command_request)) {
                    CONSOLE_ERROR("ESP32::Update", "Failed to execute SCCommand request %d/%d from ESP32.",
                                  num_requests_processed + 1, device_status.num_queued_sc_command_requests);
                    return false;
                }

                // Roll the requests queue.
                ObjectDictionary::RollQueueRequest roll_request = {
                    .queue_id = ObjectDictionary::QueueID::kQueueIDSCCommandRequests,
                    .num_items = 1,
                };
                if (!esp32.Write(ObjectDictionary::Address::kAddrRollQueue, roll_request, true)) {
                    // Require the roll request to be acknowledged.
                    CONSOLE_ERROR("ESP32::Update", "Unable to roll SCCommand request queue on ESP32.");
                    return false;
                }
                num_requests_processed++;
            }
        }

        static const uint16_t kMaxNumConsoleReadsPerUpdate = 5;
        for (uint16_t console_read_num = 0;
             console_read_num < kMaxNumConsoleReadsPerUpdate && device_status.num_queued_network_console_rx_chars > 0;
             console_read_num++) {
            // Read console message from ESP32.
            char buf[ObjectDictionary::kNetworkConsoleMessageMaxLenBytes] = {0};

            // Read as many bytes as we can without overflowing the RX queue or exceeding our buffer size or max SPI
            // transaction size.
            uint16_t bytes_to_read = MIN(
                comms_manager.esp32_console_rx_queue.MaxNumElements() - comms_manager.esp32_console_rx_queue.Length(),
                MIN(device_status.num_queued_network_console_rx_chars, sizeof(buf)));

            if (!esp32.Read(ObjectDictionary::Address::kAddrConsole, buf, bytes_to_read)) {
                CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest", "Unable to read console message from ESP32.");
                return false;
            }
            for (uint16_t i = 0; i < bytes_to_read; i++) {
                char c = (char)buf[i];
                if (!comms_manager.esp32_console_rx_queue.Push(c)) {
                    CONSOLE_ERROR("ObjectDictionary::SetBytes", "ESP32 overflowed RP2040's network console queue.");
                    comms_manager.esp32_console_rx_queue.Clear();
                    return false;
                }
            }
            ObjectDictionary::RollQueueRequest roll_request = {
                .queue_id = ObjectDictionary::QueueID::kQueueIDConsole,
                .num_items = (uint16_t)bytes_to_read,
            };
            if (!esp32.Write(ObjectDictionary::Address::kAddrRollQueue, roll_request, true)) {
                // Require the roll request to be acknowledged.
                CONSOLE_ERROR("ESP32::Update", "Unable to roll console queue after reading by %d bytes on ESP32.",
                              bytes_to_read);
                return false;
            }
            if (!esp32.Read(ObjectDictionary::Address::kAddrDeviceStatus, device_status)) {
                CONSOLE_ERROR("ESP32::Update", "Failed to re-read ESP32 device status on console read %d/%d.",
                              console_read_num + 1, kMaxNumConsoleReadsPerUpdate);
                return false;
            }
            // Successfully read console message from ESP32.
        }

#ifdef PULL_ESP32_LOG_MESSAGES
        if (device_status.num_pending_log_messages > 0) {
            // Read log messages from ESP32.
            uint8_t
                log_messages_buffer[ObjectDictionary::kLogMessageMaxNumChars * ObjectDictionary::kLogMessageQueueDepth];
            if (esp32.Read(ObjectDictionary::Address::kAddrLogMessages, log_messages_buffer,
                           device_status.pending_log_messages_packed_size_bytes)) {
                object_dictionary.UnpackLogMessages(log_messages_buffer, sizeof(log_messages_buffer),
                                                    object_dictionary.log_message_queue,
                                                    device_status.num_pending_log_messages);

                while (object_dictionary.log_message_queue.Length() > 0) {
                    ObjectDictionary::LogMessage log_message;
                    if (object_dictionary.log_message_queue.Pop(log_message)) {
                        switch (log_message.log_level) {
                            case SettingsManager::LogLevel::kInfo:
                                CONSOLE_INFO("ESP32 >>", "%.*s", log_message.num_chars, log_message.message);
                                break;
                            case SettingsManager::LogLevel::kWarnings:
                                CONSOLE_WARNING("ESP32 >>", "%.*s", log_message.num_chars, log_message.message);
                                break;
                            case SettingsManager::LogLevel::kErrors:
                                CONSOLE_ERROR("ESP32 >>", "%.*s", log_message.num_chars, log_message.message);
                                break;
                            default:
                                CONSOLE_PRINTF("ESP32 >>", "%s", log_message.num_chars, log_message.message);
                                break;
                        }
                    }
                }
            } else {
                CONSOLE_ERROR("main", "Unable to read log messages from ESP32.");
            }
        }
#endif
    }
    return true;
}

bool ESP32::ExecuteSCCommandRequest(const ObjectDictionary::SCCommandRequest &request) {
    bool write_requires_ack = false;
    switch (request.command) {
        case ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck:
            write_requires_ack = true;
            [[fallthrough]];
        case ObjectDictionary::SCCommand::kCmdWriteToSlave: {
            if (request.len == 0) {
                CONSOLE_WARNING("ESP32::ExecuteSCCommandRequest",
                                "Skipping write request to address 0x%x with zero length.", request.addr);
                return true;
            }
            switch (request.addr) {
                /** These are the addresses that the ESP32 can request a write to. **/
                case ObjectDictionary::Address::kAddrSettingsData: {
                    if (request.offset != 0) {
                        CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest",
                                      "Settings data write with non-zero offset (%d) not supported.", request.offset);
                        return false;
                    }
                    // Write settings data to ESP32.
                    if (request.len != sizeof(settings_manager.settings)) {
                        CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest",
                                      "Settings data write with invalid length (%d). Expected %d.", request.len,
                                      sizeof(settings_manager.settings));
                        return false;
                    }
                    if (!esp32.Write(request.addr, settings_manager.settings, write_requires_ack)) {
                        CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest", "Unable to write settings data to ESP32.");
                        return false;
                    }
                    break;  // Successfully wrote settings data to ESP32.
                }
                default:
                    CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest",
                                  "No implementation defined for writing to address 0x%x on slave.", request.addr);
                    return false;
            }
            break;
        }

        case ObjectDictionary::SCCommand::kCmdReadFromSlave: {
            if (request.len == 0) {
                CONSOLE_WARNING("ESP32::ExecuteSCCommandRequest",
                                "Skipping read request to address 0x%x with zero length.", request.addr);
                return true;
            }
            switch (request.addr) {
                /**  These are the addresses the ESP32 can request a read from. **/
                default:
                    CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest",
                                  "No implementation defined for reading from address 0x%x for on slave.",
                                  request.addr);
                    return false;
            }
            break;
        }
        default:
            CONSOLE_ERROR("ESP32::ExecuteSCCommandRequest", "Unsupported SCCommand received from ESP32: %d.",
                          request.command);
            return false;
    }
    return true;
}

bool ESP32::SPIGetHandshakePinLevel(bool blocking) {
    if (blocking) {
        // Make sure the ESP32 has time to lower the handshake pin after the last transaction.
        while (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ < kSPIPostTransmitLockoutUs) {
        }
        // Put CS pin LO during pre-assert interval to stop ESP32 from initiating a transaction with HANDSHAKE pin.
        SPIBeginTransaction();
        // Enforce CS pre-assert interval with blocking wait.
        uint32_t pre_assert_interval_start = get_time_since_boot_us();
        while (get_time_since_boot_us() - pre_assert_interval_start < kSPIUpdateCSPreAssertIntervalUs) {
            // Assert the CS line before the ESP32 has a chance to handshake.
            if (gpio_get(config_.spi_handshake_pin)) {
                // Allowed to exit blocking early if ESP32 asserts the HANDSHAKE pin.
                return true;
            }
        }
        return false;
    } else if (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ < kSPIPostTransmitLockoutUs) {
        // Don't actually read the handshake pin if it might overlap with an existing transaction, since we could
        // try reading the slave when nothing is here (slave hasn't yet had time to de-assert handshake pin).
        return false;
    }
    return gpio_get(config_.spi_handshake_pin);
}

int ESP32::SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes, bool end_transaction) {
    int bytes_written = 0;
#ifdef ON_PICO

    // Blocking check of handshake line. If we're expecting a handshake, it's OK for the line to be high. Otherwise, we
    // need to bail out to not stomp on the ESP32's incoming message.
    if (SPIGetHandshakePinLevel(true) && !expecting_handshake_) {
        SPIEndTransaction();  // End transaction to purge the handshake error.
        return ReturnCode::kErrorHandshakeHigh;
    }
    // Pico SDK doesn't have nice nullptr behavior for tx_buf and rx_buf, so we have to do this.
    if (tx_buf == nullptr) {
        // Transmit 0's when reading.
        bytes_written = spi_read_blocking(config_.spi_handle, 0x0, rx_buf, len_bytes);
    } else if (rx_buf == nullptr) {
        bytes_written = spi_write_blocking(config_.spi_handle, tx_buf, len_bytes);
    } else {
        bytes_written = spi_write_read_blocking(config_.spi_handle, tx_buf, rx_buf, len_bytes);
    }

    if (end_transaction) {
        SPIEndTransaction();
        // Only the last transfer chunk of the transaction is used to record the last transmission timestamp. This stops
        // transactions from getting too long as earlier chunks reset the lockout timer for later chungs, e.g. if we
        // only read one byte we don't want to wait for the timeout before conducting the rest of the transaction.
    }
    if (bytes_written < 0) {
        CONSOLE_ERROR("ESP32::SPIWriteReadBlocking", "SPI write read call returned error code 0x%x.", bytes_written);
    }
#elif defined(ON_ESP32)
    bytes_written = config_.interface.SPIWriteReadBlocking(tx_buf, rx_buf, len_bytes, end_transaction);
#endif
    return bytes_written;
}