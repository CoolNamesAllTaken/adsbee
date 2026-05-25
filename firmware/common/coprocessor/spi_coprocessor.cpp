#include "spi_coprocessor.hh"

#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hal.hh"
#elif defined(ON_coprocessor)
#include "adsbee_server.hh"

#endif

bool SPICoprocessor::Init() {
    if (!config_.interface.Init()) {
        CONSOLE_ERROR("SPICoprocessor::Init", "Failed to initialize SPI coprocessor interface.");
        return false;  // Initialization failed.
    }
#ifdef ON_COPRO_MASTER
    // Loop for a period of time to allow the device to query for settings data.
    uint32_t bootup_start_timestamp_ms = get_time_since_boot_ms();
    while (get_time_since_boot_ms() - bootup_start_timestamp_ms < SPICoprocessorSlaveInterface::kBootupDelayMs) {
        // Loop here to service the coprocessor's query for settings information when it starts up.
        Update();
    }
#endif
    return true;
}

bool SPICoprocessor::DeInit() {
    if (!config_.interface.DeInit()) {
        CONSOLE_ERROR("SPICoprocessor::DeInit", "Failed to deinitialize SPI coprocessor.");
        return false;  // Deinitialization failed.
    }

    // Don't deinit pins or SPI peripheral since some are shared by other peripherals.
    return true;
}

bool SPICoprocessor::Update() {
    bool ret = true;
#ifdef ON_COPRO_MASTER
    if (!IsEnabled()) {
        return false;  // Nothing to do.
    }

    uint32_t timestamp_ms = get_time_since_boot_ms();

    if (timestamp_ms - last_update_timestamp_ms_ <= update_interval_ms) {
        return true;  // No need to update yet.
    }
    last_update_timestamp_ms_ = timestamp_ms;

    // Rely on the slave interface to query device status and process SCCommand requests, since behavior varies by
    // device.
    if (!config_.interface.Update()) {
        CONSOLE_ERROR("SPICoprocessor::Update", "Failed to update SPI coprocessor interface.");
        return false;  // Update failed.
    }

    // Process pending SCCommand requests from the slave interface.
    if (config_.interface.num_queued_sc_command_requests > 0) {
        uint16_t num_requests_processed = 0;
        while (num_requests_processed < config_.interface.num_queued_sc_command_requests &&
               num_requests_processed < kMaxNumSCCommandRequestsPerUpdate) {
            // Read SCCommand request from coprocessor.
            ObjectDictionary::SCCommandRequest sc_command_request;
            if (!Read(ObjectDictionary::Address::kAddrSCCommandRequests, sc_command_request)) {
                CONSOLE_ERROR("SPICoprocessor::Update", "Unable to read SCCommand request %d/%d from coprocessor.",
                              num_requests_processed + 1, config_.interface.num_queued_sc_command_requests);
                return false;
            }
            // Execute the request.
            if (!ExecuteSCCommandRequest(sc_command_request)) {
                CONSOLE_ERROR("SPICoprocessor::Update", "Failed to execute SCCommand request %d/%d from coprocessor.",
                              num_requests_processed + 1, config_.interface.num_queued_sc_command_requests);
                return false;
            }

            // Roll the requests queue.
            ObjectDictionary::RollQueueRequest roll_request = {
                .queue_id = ObjectDictionary::QueueID::kQueueIDSCCommandRequests,
                .num_items = 1,
            };
            if (!Write(ObjectDictionary::Address::kAddrRollQueue, roll_request, true)) {
                // Require the roll request to be acknowledged.
                CONSOLE_ERROR("SPICoprocessor::Update", "Unable to roll SCCommand request queue on coprocessor.");
                return false;
            }
            num_requests_processed++;
        }
    }

    // Pull pending log messages from the slave interface.
    if (config_.pull_log_messages && config_.interface.num_queued_log_messages > 0) {
        // Read log messages from coprocessor.
        uint8_t log_messages_buffer[ObjectDictionary::kLogMessageMaxNumChars * ObjectDictionary::kLogMessageQueueDepth];
        if (Read(ObjectDictionary::Address::kAddrLogMessages, log_messages_buffer,
                 config_.interface.queued_log_messages_packed_size_bytes)) {
            // Acknowledge the log messages to clear the queue.

            uint16_t num_messages_pulled = object_dictionary.UnpackLogMessages(
                log_messages_buffer, sizeof(log_messages_buffer), object_dictionary.log_message_queue,
                config_.interface.num_queued_log_messages);

            ObjectDictionary::RollQueueRequest roll_request = {
                .queue_id = ObjectDictionary::QueueID::kQueueIDLogMessages, .num_items = num_messages_pulled};
            if (!Write(ObjectDictionary::Address::kAddrRollQueue, roll_request,
                       true)) {  // Require the roll request to be acknowledged.
                CONSOLE_ERROR("SPICoprocessor::Update", "Failed to roll log messages queue after reading %d messages.",
                              num_messages_pulled);
                return false;
            }

            ObjectDictionary::LogMessage log_message;
            while (object_dictionary.log_message_queue.Dequeue(log_message)) {
                if (strnlen(log_message.message, sizeof(log_message.message)) == 0) {
                    continue;  // Skip empty messages.
                }
                switch (log_message.log_level) {
                    case SettingsManager::LogLevel::kInfo:
                        CONSOLE_INFO("CoProcessor", "%s >> %s", config_.tag_str, log_message.message);
                        break;
                    case SettingsManager::LogLevel::kWarnings:
                        CONSOLE_WARNING("CoProcessor", "%s >> %s", config_.tag_str, log_message.message);
                        break;
                    case SettingsManager::LogLevel::kErrors:
                        CONSOLE_ERROR("CoProcessor", "%s >> %s", config_.tag_str, log_message.message);
                        break;
                    default:
                        CONSOLE_PRINTF("CoProcessor %s >> %s", config_.tag_str, log_message.message);
                        break;
                }
            }
        } else {
            CONSOLE_ERROR("main", "Unable to read log messages from %s.", config_.tag_str);
        }
    }
#elif defined(ON_COPRO_SLAVE) && !defined(ON_TI)
    static uint8_t rx_buf[SPICoprocessorPacket::kSPITransactionMaxLenBytes];
    memset(rx_buf, 0, SPICoprocessorPacket::kSPITransactionMaxLenBytes);

    if (!config_.interface.SPIBeginTransaction()) {
        CONSOLE_ERROR("SPICoprocessor::Update", "Failed to begin SPI transaction.");
        return false;
    }

    config_.interface.SPIUseHandshakePin(false);  // Don't solicit a transfer.
    int16_t bytes_read = SPIReadBlocking(rx_buf);
    if (bytes_read < 0) {
        bool ret = false;
        if (bytes_read != kErrorTimeout) {
            // Non-timeout errors are worth complaining about.
            CONSOLE_ERROR("SPICoprocessor::Update", "SPI read received non-timeout error code %d (%s).", bytes_read,
                          ReturnCodeToString(static_cast<ReturnCode>(bytes_read)));
        } else {
            // Timeout errors are OK and expected.
            ret = true;
        }
        config_.interface.SPIEndTransaction();
        return ret;
    }

    uint8_t cmd = rx_buf[0];
    switch (cmd) {
        case ObjectDictionary::SCCommand::kCmdWriteToSlave:
        case ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck: {
            static SPICoprocessorPacket::SCWritePacket write_packet;
            write_packet.ConstructFromBuffer(rx_buf, bytes_read);
            if (!write_packet.IsValid()) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Received unsolicited write to slave with bad checksum, packet length %d Bytes.",
                              bytes_read);
                config_.interface.SPIEndTransaction();
                return false;
            }
            ret =
                object_dictionary.SetBytes(write_packet.addr, write_packet.data, write_packet.len, write_packet.offset);
            bool ack = true;
            if (!ret) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Failed to write data for %d Byte write to slave at address 0x%x with offset %d Bytes.",
                              write_packet.len, write_packet.addr, write_packet.offset);
                ack = false;
            }
            if (cmd == ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck) {
                SPISendAck(ack);
            }
            break;
        }
        case ObjectDictionary::SCCommand::kCmdReadFromSlave: {
            static SPICoprocessorPacket::SCReadRequestPacket read_request_packet;
            read_request_packet.ConstructFromBuffer(rx_buf, bytes_read);
            if (!read_request_packet.IsValid()) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Received unsolicited read from slave with bad checksum, packet length %d Bytes.",
                              bytes_read);
                config_.interface.SPIEndTransaction();
                return false;
            }

            static SPICoprocessorPacket::SCResponsePacket response_packet;
            response_packet.cmd = ObjectDictionary::SCCommand::kCmdDataBlock;
            ret = object_dictionary.GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
                                             read_request_packet.offset);
            if (!ret) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Failed to retrieve data for %d Byte read from slave at address 0x%x",
                              read_request_packet.len, read_request_packet.addr);
                config_.interface.SPIEndTransaction();
                return false;
            }
            response_packet.data_len_bytes = read_request_packet.len;  // Assume the correct number of bytes were read.
            response_packet.PopulateCRC();
            config_.interface.SPIUseHandshakePin(true);  // Solicit a read from the RP2040.
            SPIWriteBlocking(response_packet.GetBuf(), response_packet.GetBufLenBytes());
            break;
        }
        default:
            CONSOLE_ERROR("SPICoprocessor::Update",
                          "Received unsolicited packet from RP2040 with unsupported cmd=%d, packet length %d Bytes.",
                          cmd, bytes_read);
            config_.interface.SPIEndTransaction();
            return false;
    }

    config_.interface.SPIEndTransaction();
#elif defined(ON_TI)
    // TI platform doesn't have an RTOS, so we can't block without stalling the processor. Utilize SPI callbacks for
    // primary SPI driver updates. Just update the LED here.
    config_.interface.UpdateLED();
#endif
    return ret;
}

#ifdef ON_COPRO_SLAVE
bool SPICoprocessor::LogMessage(SettingsManager::LogLevel log_level, const char* tag, const char* format,
                                va_list args) {
    // Make the scratch LogMessage static so that we don't need to allocate it all the time.
    // Allocating a LogMessage buffer on the stack can cause overflows in some limited resource event handlers.
    static ObjectDictionary::LogMessage log_message;
    log_message.log_level = log_level;
    log_message.num_chars = 0;
    log_message.message[0] = '\0';  // Initialize to empty string.

    if (strnlen(tag, ObjectDictionary::kLogMessageTagMaxNumChars) > 0) {
        log_message.num_chars += snprintf(log_message.message, ObjectDictionary::kLogMessageMaxNumChars, "[%s] ", tag);
    }

    log_message.num_chars += vsnprintf(log_message.message + log_message.num_chars,
                                       ObjectDictionary::kLogMessageMaxNumChars - log_message.num_chars, format, args);

    return object_dictionary.log_message_queue.Enqueue(log_message);
}
#endif

#ifdef ON_COPRO_MASTER

bool SPICoprocessor::ExecuteSCCommandRequest(const ObjectDictionary::SCCommandRequest& request) {
    bool write_requires_ack = false;
    switch (request.command) {
        case ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck:
            write_requires_ack = true;
            [[fallthrough]];
        case ObjectDictionary::SCCommand::kCmdWriteToSlave: {
            if (request.len == 0) {
                CONSOLE_WARNING("SPICoprocessor::ExecuteSCCommandRequest",
                                "Skipping write request to address 0x%x with zero length.", request.addr);
                return true;
            }
            switch (request.addr) {
                /** These are the addresses that the coprocessor can request a write to. **/
                case ObjectDictionary::Address::kAddrSettingsData: {
                    if (request.offset != 0) {
                        CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                                      "Settings data write with non-zero offset (%d) not supported.", request.offset);
                        return false;
                    }
                    // Write settings data to coprocessor.
                    if (request.len != sizeof(settings_manager.settings)) {
                        CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                                      "Settings data write with invalid length (%d). Expected %d.", request.len,
                                      sizeof(settings_manager.settings));
                        return false;
                    }
                    if (!Write(request.addr, settings_manager.settings, write_requires_ack)) {
                        CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                                      "Unable to write settings data to coprocessor.");
                        return false;
                    }
                    break;  // Successfully wrote settings data to coprocessor.
                }
                default:
                    CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                                  "No implementation defined for writing to address 0x%x on slave.", request.addr);
                    return false;
            }
            break;
        }

        case ObjectDictionary::SCCommand::kCmdReadFromSlave: {
            if (request.len == 0) {
                CONSOLE_WARNING("SPICoprocessor::ExecuteSCCommandRequest",
                                "Skipping read request to address 0x%x with zero length.", request.addr);
                return true;
            }
            switch (request.addr) {
                /**  These are the addresses the coprocessor can request a read from. **/
                default:
                    CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                                  "No implementation defined for reading from address 0x%x on slave.", request.addr);
                    return false;
            }
            break;
        }
        default:
            CONSOLE_ERROR("SPICoprocessor::ExecuteSCCommandRequest",
                          "Unsupported SCCommand received from coprocessor: %d.", request.command);
            return false;
    }
    return true;
}

bool SPICoprocessor::PartialWrite(ObjectDictionary::Address addr, uint8_t* object_buf, uint16_t len, uint16_t offset,
                                  bool require_ack) {
    // Guard against re-entrant calls: CONSOLE_WARNING() inside this function can trigger UpdateNetworkConsole() ->
    // esp32.Write() -> PartialWrite(), which would overwrite the shared static write_packet mid-retry.
    static bool spi_write_in_progress = false;
    static SPICoprocessorPacket::SCWritePacket write_packet;

    if (spi_write_in_progress) {
        return false;
    }
    spi_write_in_progress = true;

    write_packet.cmd = require_ack ? ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck
                                   : ObjectDictionary::SCCommand::kCmdWriteToSlave;

    write_packet.addr = addr;
    memcpy(write_packet.data, object_buf + offset, len);
    write_packet.len = len;
    write_packet.offset = offset;
    write_packet.PopulateCRC();

    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
        // Don't end the transaction yet to allow recovery of packets from kErrorHandshakeHigh.
        int bytes_written = SPIWriteBlocking(write_packet.GetBuf(), write_packet.GetBufLenBytes(), true);

        if (bytes_written < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d (%s) while writing object over SPI.",
                     bytes_written, ReturnCodeToString(static_cast<ReturnCode>(bytes_written)));

            goto PARTIAL_WRITE_FAILED;
        }
        if (require_ack && !SPIWaitForAck()) {
            snprintf(error_message, kErrorMessageMaxLen, "Timed out or received bad ack after writing to coprocessor.");
            goto PARTIAL_WRITE_FAILED;
        }
        // Completed successfully!
        ret = true;
        break;
    PARTIAL_WRITE_FAILED:
        CONSOLE_WARNING("SPICoprocessor::PartialWrite", "%s", error_message);
        num_attempts++;
        ret = false;
        continue;
    }
    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Failed after %d tries: %s", num_attempts, error_message);
    }
    spi_write_in_progress = false;
    return ret;
}

bool SPICoprocessor::PartialRead(ObjectDictionary::Address addr, uint8_t* object_buf, uint16_t len, uint16_t offset) {
    static bool spi_read_in_progress = false;
    static SPICoprocessorPacket::SCReadRequestPacket read_request_packet;

    if (spi_read_in_progress) {
        return false;
    }
    spi_read_in_progress = true;

    read_request_packet.cmd = ObjectDictionary::SCCommand::kCmdReadFromSlave;

    read_request_packet.addr = addr;
    read_request_packet.offset = offset;
    read_request_packet.len = len;
    read_request_packet.PopulateCRC();

    static uint8_t rx_buf[SPICoprocessorPacket::kSPITransactionMaxLenBytes];

    uint16_t read_request_bytes = read_request_packet.GetBufLenBytes();

    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    static SPICoprocessorPacket::SCResponsePacket response_packet;
    while (num_attempts < kSPITransactionMaxNumRetries) {
        // On the master, reading from the slave is two transactions: The read request is sent, then we wait on the
        // handshake line to read the reply.

        // Don't end transaction in order to allow recovery from kErrorHandshakeHigh error.
        int bytes_written = SPIWriteBlocking(read_request_packet.GetBuf(), read_request_bytes, true);
        int bytes_read = 0;
        if (bytes_written < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d (%s) while writing read request over SPI.",
                     bytes_written, ReturnCodeToString(static_cast<ReturnCode>(bytes_written)));
            goto PARTIAL_READ_FAILED;
        }
        if (!config_.interface.SPIWaitForHandshake()) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Timed out while waiting for handshake after sending read request.");
            goto PARTIAL_READ_FAILED;
        }

        response_packet.data_len_bytes =
            len;  // We need to set this manually since we are using the default constructor.
        bytes_read = SPIReadBlocking(response_packet.GetBuf(),
                                     SPICoprocessorPacket::SCResponsePacket::GetBufLenForPayloadLenBytes(len));
        if (bytes_read < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d (%s) while reading read response over SPI.",
                     bytes_read, ReturnCodeToString(static_cast<ReturnCode>(bytes_written)));
            goto PARTIAL_READ_FAILED;
        }

        if (!response_packet.IsValid()) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Received response packet of length %d Bytes with an invalid CRC.",
                     response_packet.GetBufLenBytes());
            goto PARTIAL_READ_FAILED;
        }
        if (response_packet.cmd != ObjectDictionary::SCCommand::kCmdDataBlock) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Received invalid response with cmd=0x%x to requested read at address 0x%x of length %d with "
                     "offset %d Bytes.",
                     response_packet.cmd, read_request_packet.addr, read_request_packet.len,
                     read_request_packet.offset);
            goto PARTIAL_READ_FAILED;
        }
        if (response_packet.data_len_bytes != len) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Received incorrect number of Bytes while reading object at address 0x%x with offset %d "
                     "Bytes. Requested %d Bytes but received %d.",
                     addr, offset, read_request_packet.len, response_packet.data_len_bytes);
            goto PARTIAL_READ_FAILED;
        }
        // Completed successfully!
        ret = true;
        memcpy(object_buf + offset, response_packet.data, response_packet.data_len_bytes);
        break;
    PARTIAL_READ_FAILED:
        CONSOLE_WARNING("SPICoprocessor::PartialRead", "%s", error_message);
        num_attempts++;
        ret = false;
        continue;
    }

    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed after %d tries: %s", num_attempts, error_message);
    }
    spi_read_in_progress = false;
    return ret;
}

bool SPICoprocessor::SPIWaitForAck() {
    static bool ack_wait_in_progress = false;
    static SPICoprocessorPacket::SCAckPacket ack_packet;

    if (ack_wait_in_progress) {
        return false;
    }
    ack_wait_in_progress = true;

    if (!config_.interface.SPIWaitForHandshake()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Timed out while waiting for ack: never received handshake.");
        ack_wait_in_progress = false;
        return false;
    }

    // We need to call SPIReadBlocking without ending the transaction in case we want to recover a
    // kErrorHandshakeHigh error.
    int bytes_read =
        SPIReadBlocking(ack_packet.GetBuf(), SPICoprocessorPacket::SCAckPacket::kBufLenBytes, true);

    if (bytes_read < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "SPI read failed with code %d (%s).", bytes_read,
                      ReturnCodeToString(static_cast<ReturnCode>(bytes_read)));
        ack_wait_in_progress = false;
        return false;
    }
    if (ack_packet.cmd != ObjectDictionary::SCCommand::kCmdAck) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck",
                      "Received a message that was not an ack (cmd=0x%x, expected 0x%x).", ack_packet.cmd,
                      ObjectDictionary::SCCommand::kCmdAck);
        ack_wait_in_progress = false;
        return false;
    }
    if (!ack_packet.IsValid()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Received a response packet with an invalid CRC.");
        ack_wait_in_progress = false;
        return false;
    }
    ack_wait_in_progress = false;
    return ack_packet.ack;
}

#ifdef HARDWARE_UNIT_TESTS
bool SPICoprocessor::TestSPIPersistentDesync() {
    // Replicates the production SPI deadlock: rapid consecutive recovery cycles interleaved with
    // the UpdateNetworkConsole writes that fire via CONSOLE_WARNING during PartialRead retries.
    // The existing TestSPIHandshakeDeadlock verifies single-shot recovery works. This test stresses
    // the ESP32 SPI DMA with back-to-back partial-transaction completions to check whether the DMA
    // state accumulates into a stuck spi_slave_transmit (spi_mutex_ held forever, ESP32 alive but
    // unable to serve SPI).

    // Phase 1: baseline sanity check.
    ObjectDictionary::ESP32DeviceStatus baseline_status;
    if (!Read(ObjectDictionary::Address::kAddrDeviceStatus, baseline_status)) {
        CONSOLE_ERROR("TestSPIPersistentDesync", "ABORT: Baseline read failed before test began.");
        return false;
    }
    CONSOLE_INFO("TestSPIPersistentDesync", "Baseline OK. Starting desync stress loop...");

    static const int kNumDesyncIterations = 20;
    for (int i = 0; i < kNumDesyncIterations; i++) {
        // Step a: send a read request so the ESP32 queues a response and raises the handshake.
        SPICoprocessorPacket::SCReadRequestPacket req;
        req.cmd = ObjectDictionary::SCCommand::kCmdReadFromSlave;
        req.addr = ObjectDictionary::Address::kAddrDeviceStatus;
        req.offset = 0;
        req.len = sizeof(ObjectDictionary::ESP32DeviceStatus);
        req.PopulateCRC();
        int sent = SPIWriteBlocking(req.GetBuf(), req.GetBufLenBytes(), /*end_transaction=*/true);
        if (sent < 0) {
            CONSOLE_WARNING("TestSPIPersistentDesync", "Iter %d: read-request write failed (%d), continuing.", i, sent);
            continue;
        }

        // Step b: busy-wait half the handshake timeout — long enough for the ESP32 to have queued
        // its response and raised the handshake, but short enough that we never call
        // SPIWaitForHandshake() and consume it cleanly.
        uint32_t wait_start_ms = get_time_since_boot_ms();
        while (get_time_since_boot_ms() - wait_start_ms < SPICoprocessorSlaveInterface::kSPIHandshakeTimeoutMs / 2) {
        }

        // Step c: without checking the handshake, attempt a scratch write — this sees handshake
        // HIGH with expecting_handshake_=false, clocks 4 dummy bytes (recovery), and returns
        // kErrorHandshakeHigh. This is the same path taken by UpdateNetworkConsole→PartialWrite
        // when it fires during a PartialRead failure.
        static const uint8_t kScratchPayload[] = {0xDE, 0xAD, 0xBE, 0xEF};
        SPICoprocessorPacket::SCWritePacket scratch;
        scratch.cmd = ObjectDictionary::SCCommand::kCmdWriteToSlave;
        scratch.addr = ObjectDictionary::Address::kAddrScratch;
        scratch.len = sizeof(kScratchPayload);
        scratch.offset = 0;
        memcpy(scratch.data, kScratchPayload, sizeof(kScratchPayload));
        scratch.PopulateCRC();
        int write_result = SPIWriteBlocking(scratch.GetBuf(), scratch.GetBufLenBytes(), /*end_transaction=*/true);
        CONSOLE_INFO("TestSPIPersistentDesync", "Iter %d: desync write result %d (expect %d=kErrorHandshakeHigh).", i,
                     write_result, ReturnCode::kErrorHandshakeHigh);

        // Step d: simulate UpdateNetworkConsole by enqueuing console chars and flushing them.
        // In production, every CONSOLE_WARNING inside a PartialRead retry loop triggers exactly
        // this path.
        const char* fake_error = "TestSPIPersistentDesync: simulated console error message\r\n";
        for (const char* p = fake_error; *p; p++) {
            comms_manager.esp32_console_tx_queue.Enqueue(*p);
        }
        comms_manager.UpdateNetworkConsole();

        // Step e: immediately attempt a PartialRead — this is the "retry" that should succeed but
        // may fail under accumulated DMA stress.
        ObjectDictionary::ESP32DeviceStatus iter_status;
        if (!Read(ObjectDictionary::Address::kAddrDeviceStatus, iter_status)) {
            CONSOLE_WARNING("TestSPIPersistentDesync", "Iter %d: PartialRead failed after desync.", i);
        } else {
            CONSOLE_INFO("TestSPIPersistentDesync", "Iter %d: PartialRead succeeded after desync.", i);
        }
    }

    // Phase 3: recovery check — if the deadlock was triggered, all reads will fail here.
    CONSOLE_INFO("TestSPIPersistentDesync", "Desync loop complete. Checking for deadlock...");
    static const int kMaxRecoveryAttempts = 30;
    bool recovered = false;
    for (int attempt = 0; attempt < kMaxRecoveryAttempts; attempt++) {
        ObjectDictionary::ESP32DeviceStatus check_status;
        if (Read(ObjectDictionary::Address::kAddrDeviceStatus, check_status)) {
            recovered = true;
            CONSOLE_INFO("TestSPIPersistentDesync", "Recovered on attempt %d/%d.", attempt + 1,
                         kMaxRecoveryAttempts);
            break;
        }
        uint32_t delay_start = get_time_since_boot_ms();
        while (get_time_since_boot_ms() - delay_start < 100) {
        }
    }

    // Phase 4: handshake-stuck diagnostic — if the ESP32's spi_slave_transmit is blocked, the
    // handshake pin will be held HIGH continuously.
    uint32_t diag_start_ms = get_time_since_boot_ms();
    uint32_t high_count = 0;
    uint32_t sample_count = 0;
    while (get_time_since_boot_ms() - diag_start_ms < 1000) {
        if (config_.interface.SPIGetHandshakePinLevel()) {
            high_count++;
        }
        sample_count++;
        uint32_t sample_delay = get_time_since_boot_ms();
        while (get_time_since_boot_ms() - sample_delay < 10) {
        }
    }
    uint32_t handshake_high_pct = sample_count > 0 ? (high_count * 100 / sample_count) : 0;
    CONSOLE_INFO("TestSPIPersistentDesync", "Handshake HIGH %lu%% of 1s diagnostic window (%lu/%lu samples).",
                 handshake_high_pct, high_count, sample_count);
    if (handshake_high_pct > 90) {
        CONSOLE_ERROR("TestSPIPersistentDesync",
                      "DEADLOCK CONFIRMED: handshake stuck HIGH — ESP32 spi_slave_transmit is blocked.");
    }

    if (!recovered) {
        CONSOLE_ERROR("TestSPIPersistentDesync",
                      "DEADLOCK REPRODUCED: SPI communication lost after %d desync iterations. "
                      "System left in deadlocked state for observation. Power cycle to recover.",
                      kNumDesyncIterations);
    } else {
        CONSOLE_INFO("TestSPIPersistentDesync",
                     "No deadlock: system recovered after stress loop. "
                     "Handshake stuck %lu%% of diagnostic window.",
                     handshake_high_pct);
    }
    return recovered;
}

bool SPICoprocessor::TestSPIHandshakeDeadlock() {
    // Step 1: Send a read request so the ESP32 queues a response and raises its handshake pin.
    // We deliberately skip SPIWaitForHandshake() so expecting_handshake_ stays false.
    SPICoprocessorPacket::SCReadRequestPacket request;
    request.cmd = ObjectDictionary::SCCommand::kCmdReadFromSlave;
    request.addr = ObjectDictionary::Address::kAddrDeviceStatus;
    request.offset = 0;
    request.len = sizeof(ObjectDictionary::ESP32DeviceStatus);
    request.PopulateCRC();
    int bytes = SPIWriteBlocking(request.GetBuf(), request.GetBufLenBytes(), /*end_transaction=*/true);
    if (bytes < 0) {
        CONSOLE_ERROR("TestSPIHandshakeDeadlock", "Failed to send read request (code %d).", bytes);
        return false;
    }

    // Step 2: Wait past the handshake timeout. The ESP32 prepares its response and raises the handshake
    // during this window, but we never set expecting_handshake_ = true, so SPIBeginTransaction will
    // treat it as an unexpected high.
    uint32_t delay_start_ms = get_time_since_boot_ms();
    while (get_time_since_boot_ms() - delay_start_ms <
           SPICoprocessorSlaveInterface::kSPIHandshakeTimeoutMs + 10) {
    }

    // Step 3: Attempt a harmless write. The first try will see handshake HIGH with expecting_handshake_
    // = false and return kErrorHandshakeHigh. With the dummy-byte recovery fix, this clocks enough
    // SCLK edges to complete the ESP32's pending spi_slave_transmit, lowering the handshake so the
    // retry can succeed. Without the fix, this deadlocks permanently.
    CONSOLE_INFO("TestSPIHandshakeDeadlock",
                 "Handshake should be HIGH. Attempting write to trigger recovery...");
    uint8_t dummy[4] = {0};
    bool recovered = PartialWrite(ObjectDictionary::Address::kAddrScratch, dummy, sizeof(dummy));
    if (recovered) {
        CONSOLE_INFO("TestSPIHandshakeDeadlock", "Recovery succeeded — deadlock fix is working.");
    } else {
        CONSOLE_ERROR("TestSPIHandshakeDeadlock", "Recovery failed — system may be deadlocked.");
    }
    return recovered;
}
#endif

#endif

#ifdef ON_COPRO_SLAVE
bool SPICoprocessor::SPISendAck(bool success) {
    static SPICoprocessorPacket::SCAckPacket ack_packet;
    ack_packet.ack = success;
    ack_packet.PopulateCRC();
    config_.interface.SPIUseHandshakePin(true);  // Solicit a transfer to send the ack.
#ifndef ON_TI
    return SPIWriteBlocking(ack_packet.GetBuf(), SPICoprocessorPacket::SCAckPacket::kBufLenBytes) > 0;
#else
    return SPIWriteNonBlocking(ack_packet.GetBuf(), SPICoprocessorPacket::SCAckPacket::kBufLenBytes) > 0;
#endif  // ON_TI
}
#endif  // ON_COPRO_SLAVE