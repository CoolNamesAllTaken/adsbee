#include "spi_coprocessor.hh"

#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hal.hh"
#elif defined(ON_ESP32)
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
        // Loop here to service the ESP32's query for settings information when it starts up.
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

bool SPICoprocessor::Update(bool blocking) {
    bool ret = false;
#ifdef ON_COPRO_MASTER
    if (!IsEnabled()) {
        return false;  // Nothing to do.
    }
    // Do a blocking check of the HANDSHAKE pin to make sure that the ESP32 can have its say.
    if (!config_.interface.SPIGetHandshakePinLevel(blocking)) {
        return true;  // Nothing to do.
    }

    // Incoming unsolicited transmission from ESP32.
    uint8_t rx_buf[kSPITransactionMaxLenBytes];
    config_.interface.SPIWaitForHandshake();                  // Call this to get expect_handshake_ set to true.
    uint16_t bytes_read = SPIReadBlocking(rx_buf, 1, false);  // Peek the command first, keep chip select asserted.
    if (bytes_read < 0) {
        CONSOLE_ERROR("SPICoprocessor::Update", "SPI command read received non-timeout error code %d (%s).", bytes_read,
                      ReturnCodeToString(static_cast<ReturnCode>(bytes_read)));
        ret = false;
    } else if (bytes_read == 0) {
        CONSOLE_ERROR("SPICoprocessor::Update", "SPI command read received 0 Bytes, no command received.");
        ret = false;
    } else {
        SCCommand cmd = static_cast<SCCommand>(rx_buf[0]);
        switch (cmd) {
            case kCmdWriteToMaster:
            case kCmdWriteToMasterRequireAck: {
                // Figure out how long the write packet is, then read in the rest of it.
                SPIReadBlocking(rx_buf + sizeof(SCCommand), SCWritePacket::kDataOffsetBytes - sizeof(SCCommand),
                                false);  // Read addr, offset, and len.
                uint16_t len;
                memcpy(&len, rx_buf + SCWritePacket::kDataOffsetBytes - sizeof(uint16_t), sizeof(uint16_t));
                // Read the rest of the write packet and complete the transaction. Guard to not run off end if invalid
                // len is received.
                SPIReadBlocking(rx_buf + SCWritePacket::kDataOffsetBytes,
                                MIN(len, SCWritePacket::kDataMaxLenBytes) + SCPacket::kCRCLenBytes, true);
                SCWritePacket write_packet =
                    SCWritePacket(rx_buf, SCWritePacket::kDataOffsetBytes + len + SCPacket::kCRCLenBytes);
                if (!write_packet.IsValid()) {
                    CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited write to master with bad checksum.");
                    return false;
                }
                ret = object_dictionary.SetBytes(write_packet.addr, write_packet.data, write_packet.len,
                                                 write_packet.offset);
                bool ack = true;
                if (!ret) {
                    CONSOLE_ERROR(
                        "SPICoprocessor::Update",
                        "Failed to write data for write to slave at address 0x%x with offset %d and length %d Bytes.",
                        write_packet.addr, write_packet.offset, write_packet.len);
                    ack = false;
                }
                if (write_packet.cmd == kCmdWriteToMasterRequireAck) {
                    SPISendAck(ack);
                }
                break;
            }
            case kCmdReadFromMaster: {
                // NOTE: If an Object lager than SCResponsePacket::kDataMaxLenBytes - SCReadRequestPacket::kBufLenBytes,
                // the slave must request multiple reads with offsets to read the full object.
                SPIReadBlocking(rx_buf + sizeof(SCCommand), SCReadRequestPacket::kBufLenBytes - sizeof(SCCommand),
                                false);
                SCReadRequestPacket read_request_packet =
                    SCReadRequestPacket(rx_buf, SCReadRequestPacket::kBufLenBytes);
                if (!read_request_packet.IsValid()) {
                    config_.interface.SPIEndTransaction();
                    CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited read from master with bad checksum.");
                    return false;
                }
                SCResponsePacket response_packet;
                response_packet.cmd = kCmdDataBlock;
                ret = object_dictionary.GetBytes(read_request_packet.addr, response_packet.data,
                                                 read_request_packet.len, read_request_packet.offset);
                if (!ret) {
                    CONSOLE_ERROR("SPICoprocessor::Update",
                                  "Failed to retrieve data for read from master at address 0x%x with length %d Bytes.",
                                  read_request_packet.addr, read_request_packet.len);
                }
                response_packet.data_len_bytes = read_request_packet.len;
                response_packet.PopulateCRC();
                SPIWriteBlocking(response_packet.GetBuf(), response_packet.GetBufLenBytes());
                break;
            }
            default:
                config_.interface.SPIEndTransaction();
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Received unsolicited packet from ESP32 with unsupported cmd=%d.", cmd);
                return false;
        }
    }
#elif defined(ON_COPRO_SLAVE)
    // TODO: Return if not blocking and no transaction is pending.
    uint8_t rx_buf[kSPITransactionMaxLenBytes];
    memset(rx_buf, 0, kSPITransactionMaxLenBytes);

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
        case kCmdWriteToSlave:
        case kCmdWriteToSlaveRequireAck: {
            SCWritePacket write_packet = SCWritePacket(rx_buf, bytes_read);
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
            if (cmd == kCmdWriteToSlaveRequireAck) {
                SPISendAck(ack);
            }
            break;
        }
        case kCmdReadFromSlave: {
            SCReadRequestPacket read_request_packet = SCReadRequestPacket(rx_buf, bytes_read);
            if (!read_request_packet.IsValid()) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Received unsolicited read from slave with bad checksum, packet length %d Bytes.",
                              bytes_read);
                config_.interface.SPIEndTransaction();
                return false;
            }

            SCResponsePacket response_packet;
            response_packet.cmd = kCmdDataBlock;
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

#endif

    config_.interface.SPIEndTransaction();
    return ret;
}

#if defined(ON_ESP32) || defined(ON_TI)
bool SPICoprocessor::LogMessage(SettingsManager::LogLevel log_level, const char *tag, const char *format,
                                va_list args) {
    // Make the scratch LogMessage static so that we don't need to allocate it all the time.
    // Allocating a LogMessage buffer on the stack can cause overflows in some limited resource event handlers.
    static ObjectDictionary::LogMessage log_message;
    log_message.log_level = log_level;
    log_message.num_chars = 0;
    log_message.message[0] = '\0';  // Initialize to empty string.

    log_message.num_chars += snprintf(log_message.message, ObjectDictionary::kLogMessageMaxNumChars, "[%s] ", tag);
    log_message.num_chars += vsnprintf(log_message.message + log_message.num_chars,
                                       ObjectDictionary::kLogMessageMaxNumChars - log_message.num_chars, format, args);

    return object_dictionary.log_message_queue.Push(log_message);
}
#endif

/** Begin Private Functions **/

bool SPICoprocessor::SPISendAck(bool success) {
    SCResponsePacket response_packet;
    response_packet.cmd = kCmdAck;
    response_packet.data[0] = success;
    response_packet.data_len_bytes = 1;
    response_packet.PopulateCRC();
#ifdef ON_ESP32
    config_.interface.SPIUseHandshakePin(true);  // Solicit a transfer to send the ack.
#endif
    return SPIWriteBlocking(response_packet.GetBuf(), SCResponsePacket::kAckLenBytes) > 0;
}

bool SPICoprocessor::SPIWaitForAck() {
    SCResponsePacket response_packet;
#ifdef ON_PICO
    if (!config_.interface.SPIWaitForHandshake()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Timed out while waiting for ack: never received handshake.");
        return false;
    }
#elif defined(ON_ESP32)
    config_.interface.SPIUseHandshakePin(false);  // Don't solicit an ack when waiting for one.
#endif
    // We need to call SPIReadBlocking without ending the transaction in case we want to recover a kErrorHandshakeHigh
    // error.
    int bytes_read = SPIReadBlocking(response_packet.GetBuf(), SCResponsePacket::kAckLenBytes, false);
    response_packet.data_len_bytes = SCResponsePacket::kAckLenBytes;
#ifdef ON_COPRO_MASTER
    if (bytes_read == kErrorHandshakeHigh) {
        // If we stepped on the slave while trying to talk, our transaction is moot but at least we can avoid
        // wasting the packet from the slave.
        // Get the slave interface to expect a handshake high.
        config_.interface.SPIWaitForHandshake();
        Update(true);
    }
#endif
    config_.interface.SPIEndTransaction();
    if (bytes_read < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "SPI read failed with code %d (%s).", bytes_read,
                      ReturnCodeToString(static_cast<ReturnCode>(bytes_read)));
        return false;
    }
    if (response_packet.cmd != kCmdAck) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck",
                      "Received a message that was not an ack (cmd=0x%x, expected 0x%x).", response_packet.cmd,
                      kCmdAck);
        return false;
    }
    if (!response_packet.IsValid()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Received a response packet with an invalid CRC.");
        return false;
    }
    return response_packet.data[0];  // Return ACK / NACK value.
}

int SPICoprocessor::SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes, bool end_transaction) {
    return config_.interface.SPIWriteReadBlocking(tx_buf, rx_buf, len_bytes, end_transaction);
}

bool SPICoprocessor::PartialWrite(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset,
                                  bool require_ack) {
    SCWritePacket write_packet;
#ifdef ON_COPRO_MASTER
    write_packet.cmd = require_ack ? kCmdWriteToSlaveRequireAck : kCmdWriteToSlave;
#elif defined(ON_COPRO_SLAVE)
    write_packet.cmd = require_ack ? kCmdWriteToMasterRequireAck : kCmdWriteToMaster;
#else
    return false;  // Not supported on other platforms.
#endif
    write_packet.addr = addr;
    memcpy(write_packet.data, object_buf + offset, len);
    write_packet.len = len;
    write_packet.offset = offset;
    write_packet.PopulateCRC();

#ifdef ON_COPRO_SLAVE
    if (!config_.interface.SPIBeginTransaction()) {
        CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Failed to begin SPI transaction.");
        return false;  // Failed to begin transaction.
    }
#endif
    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
#ifdef ON_COPRO_MASTER
        // Call Update with blocking to flush ESP32 of messages before write (block to make sure it has a chance to
        // talk if it needs to).
        Update(true);  // Check to see if handshake line is raised before blasting a packet into the ESP32.
#elif defined(ON_COPRO_SLAVE)
        // Handshake pin gets set LO by SPIWaitForAck(), so we need to re-assert it here for retries to bring it HI.
        config_.interface.SPIUseHandshakePin(true);  // Set handshake pin to solicit a transaction with the RP2040.
#endif
        // Don't end the transaction yet to allow recovery of packets from kErrorHandshakeHigh.
        int bytes_written = SPIWriteBlocking(write_packet.GetBuf(), write_packet.GetBufLenBytes(), false);
#ifdef ON_COPRO_MASTER
        if (bytes_written == ReturnCode::kErrorHandshakeHigh) {
            // Oops, didn't see you there! Go ahead and say what you wanted to.
            // Get the slave interface to expect a handshake high.
            config_.interface.SPIWaitForHandshake();
            Update(true);
        }
#endif
        config_.interface.SPIEndTransaction();
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
#ifdef ON_COPRO_SLAVE
    config_.interface.SPIEndTransaction();  // End the SPI transaction on the slave.
#endif
    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Failed after %d tries: %s", num_attempts, error_message);
    }
    return ret;
}

bool SPICoprocessor::PartialRead(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset) {
    SCReadRequestPacket read_request_packet;
#ifdef ON_COPRO_MASTER
    read_request_packet.cmd = kCmdReadFromSlave;
#elif defined(ON_COPRO_SLAVE)
    read_request_packet.cmd = kCmdReadFromMaster;
#else
    return false;  // Not supported on other platforms.
#endif
    read_request_packet.addr = addr;
    read_request_packet.offset = offset;
    read_request_packet.len = len;
    read_request_packet.PopulateCRC();

    uint8_t rx_buf[kSPITransactionMaxLenBytes];

    uint16_t read_request_bytes = read_request_packet.GetBufLenBytes();

#ifdef ON_COPRO_SLAVE
    if (!config_.interface.SPIBeginTransaction()) {
        CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed to begin SPI transaction.");
        return false;  // Failed to begin transaction.
    }
#endif

    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
#ifdef ON_COPRO_MASTER
        // On the master, reading from the slave is two transactions: The read request is sent, then we wait on the
        // handshake line to read the reply.
        SCResponsePacket response_packet;  // Declare this up here so the goto's don't cross it.
        // Call Update with blocking to flush ESP32 of messages before write (block to make sure it has a chance to
        // talk
        // if it needs to).
        Update(true);  // Check to see if handshake line is raised before blasting a packet into the ESP32.
        // Don't end transaction in order to allow recovery from kErrorHandshakeHigh error.
        int bytes_written = SPIWriteBlocking(read_request_packet.GetBuf(), read_request_bytes, false);
        if (bytes_written == ReturnCode::kErrorHandshakeHigh) {
            // Oops, didn't see you there! Go ahead and say what you wanted to.
            // Get the slave interface to expect a handshake high.
            config_.interface.SPIWaitForHandshake();
            Update(true);
        }
        config_.interface.SPIEndTransaction();
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
        bytes_read = SPIReadBlocking(response_packet.GetBuf(), SCResponsePacket::GetBufLenForPayloadLenBytes(len));
        if (bytes_read < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d (%s) while reading read response over SPI.",
                     bytes_read, ReturnCodeToString(static_cast<ReturnCode>(bytes_written)));
            goto PARTIAL_READ_FAILED;
        }
#elif defined(ON_COPRO_SLAVE)
        // On the slave, reading from the master is a single transaction. We preload the beginning of the message
        // with the read request, and the master populates the remainder of the message with the reply.
        config_.interface.SPIUseHandshakePin(true);  // Set handshake pin to solicit a transaction with the RP2040.
        // Need to request the max transaction size. If we request something smaller, like read_request_bytes (which
        // doesn't include the response bytes), the SPI transmit function won't write the additional reply into our
        // buffer.
        int bytes_exchanged =
            SPIWriteReadBlocking(read_request_packet.GetBuf(), rx_buf, SCPacket::kPacketMaxLenBytes, false);

        if (bytes_exchanged < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d (%s) during read from master SPI transaction.",
                     bytes_exchanged, ReturnCodeToString(static_cast<ReturnCode>(bytes_exchanged)));
            // Can't use the goto shortcut here because it would cross over response_packet initialization.
            CONSOLE_WARNING("SPICoprocessor::PartialRead", "%s", error_message);
            num_attempts++;
            ret = false;
            // Mutex can be given back immediately because we don't ever wait for an ACK.
            config_.interface.SPIEndTransaction();
            if (!config_.interface.SPIBeginTransaction()) {
                CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed to begin SPI while retrying partial read.");
                return false;  // Failed to begin transaction.
            }
            continue;
        }
        if (bytes_exchanged <= read_request_bytes) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "SPI transaction was too short, request was %d Bytes, only exchanged %d Bytes including "
                     "request and response.",
                     read_request_bytes, bytes_exchanged);
            // Can't use the goto shortcut here because it would cross over response_packet initialization.
            CONSOLE_WARNING("SPICoprocessor::PartialRead", "%s", error_message);
            num_attempts++;
            ret = false;
            // Mutex can be given back immediately because we don't ever wait for an ACK.
            config_.interface.SPIEndTransaction();
            if (!config_.interface.SPIBeginTransaction()) {
                CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed to begin SPI while retrying partial read.");
                return false;  // Failed to begin transaction.
            }
            continue;
        }
        SCResponsePacket response_packet =
            SCResponsePacket(rx_buf + read_request_bytes, bytes_exchanged - read_request_bytes);
#else
        SCResponsePacket response_packet;  // Dummy to stop compile errors.
        // Total BS used to suppress a compile warning during host unit tests.
        rx_buf[read_request_bytes] = '\0';
        printf("%s", rx_buf);
#endif
        if (!response_packet.IsValid()) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Received response packet of length %d Bytes with an invalid CRC.",
                     response_packet.GetBufLenBytes());
            goto PARTIAL_READ_FAILED;
        }
        if (response_packet.cmd != SCCommand::kCmdDataBlock) {
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
#ifdef ON_COPRO_SLAVE
    // Allow other tasks to access the SPI peripheral.
    config_.interface.SPIEndTransaction();  // End the SPI transaction on the slave.
#endif
    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed after %d tries: %s", num_attempts, error_message);
    }
    return ret;
}