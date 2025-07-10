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

bool SPICoprocessor::Update() {
    bool ret = false;
#ifdef ON_COPRO_MASTER
    if (!IsEnabled()) {
        return false;  // Nothing to do.
    }

    // There are no unsolicited messages from the slave. Just make sure the underlying interface gets poked.
    if (!config_.interface.Update()) {
        CONSOLE_ERROR("SPICoprocessor::Update", "Failed to update SPI coprocessor interface.");
        return false;  // Update failed.
    }

    config_.interface.SPIEndTransaction();
#elif defined(ON_COPRO_SLAVE) && !defined(ON_TI)
    uint8_t rx_buf[SPICoprocessorPacket::kSPITransactionMaxLenBytes];
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
            SPICoprocessorPacket::SCWritePacket write_packet = SPICoprocessorPacket::SCWritePacket(rx_buf, bytes_read);
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
            SPICoprocessorPacket::SPICoprocessorPacket::SCReadRequestPacket read_request_packet =
                SPICoprocessorPacket::SCReadRequestPacket(rx_buf, bytes_read);
            if (!read_request_packet.IsValid()) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Received unsolicited read from slave with bad checksum, packet length %d Bytes.",
                              bytes_read);
                config_.interface.SPIEndTransaction();
                return false;
            }

            SPICoprocessorPacket::SCResponsePacket response_packet;
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
#else
    // TI platform doesn't have an RTOS, so we can't block without stalling the processor. Utilize SPI callback updates
    // instead.
#endif
    return ret;
}

#ifdef ON_COPRO_SLAVE
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

/** Begin Protected Functions **/

#ifdef ON_COPRO_MASTER

bool SPICoprocessor::PartialWrite(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset,
                                  bool require_ack) {
    SPICoprocessorPacket::SCWritePacket write_packet;

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
    return ret;
}

bool SPICoprocessor::PartialRead(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset) {
    SPICoprocessorPacket::SCReadRequestPacket read_request_packet;

    read_request_packet.cmd = ObjectDictionary::SCCommand::kCmdReadFromSlave;

    read_request_packet.addr = addr;
    read_request_packet.offset = offset;
    read_request_packet.len = len;
    read_request_packet.PopulateCRC();

    uint8_t rx_buf[SPICoprocessorPacket::kSPITransactionMaxLenBytes];

    uint16_t read_request_bytes = read_request_packet.GetBufLenBytes();

    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
        // On the master, reading from the slave is two transactions: The read request is sent, then we wait on the
        // handshake line to read the reply.
        SPICoprocessorPacket::SCResponsePacket response_packet;  // Declare this up here so the goto's don't cross it.

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
    return ret;
}

bool SPICoprocessor::SPIWaitForAck() {
    SPICoprocessorPacket::SCResponsePacket response_packet;

    if (!config_.interface.SPIWaitForHandshake()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Timed out while waiting for ack: never received handshake.");
        return false;
    }

    // We need to call SPIReadBlocking without ending the transaction in case we want to recover a kErrorHandshakeHigh
    // error.
    int bytes_read =
        SPIReadBlocking(response_packet.GetBuf(), SPICoprocessorPacket::SCResponsePacket::kAckLenBytes, true);
    response_packet.data_len_bytes = SPICoprocessorPacket::SCResponsePacket::kAckLenBytes;

    if (bytes_read < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "SPI read failed with code %d (%s).", bytes_read,
                      ReturnCodeToString(static_cast<ReturnCode>(bytes_read)));
        return false;
    }
    if (response_packet.cmd != ObjectDictionary::SCCommand::kCmdAck) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck",
                      "Received a message that was not an ack (cmd=0x%x, expected 0x%x).", response_packet.cmd,
                      ObjectDictionary::SCCommand::kCmdAck);
        return false;
    }
    if (!response_packet.IsValid()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Received a response packet with an invalid CRC.");
        return false;
    }
    return response_packet.data[0];  // Return ACK / NACK value.
}
#endif

bool SPICoprocessor::SPISendAck(bool success) {
    SPICoprocessorPacket::SCResponsePacket response_packet;
    response_packet.cmd = ObjectDictionary::ObjectDictionary::SCCommand::kCmdAck;
    response_packet.data[0] = success;
    response_packet.data_len_bytes = 1;
    response_packet.PopulateCRC();
    config_.interface.SPIUseHandshakePin(true);  // Solicit a transfer to send the ack.
#ifndef ON_TI
    return SPIWriteBlocking(response_packet.GetBuf(), SPICoprocessorPacket::SCResponsePacket::kAckLenBytes) > 0;
#else
    return SPIWriteNonBlocking(response_packet.GetBuf(), SPICoprocessorPacket::SCResponsePacket::kAckLenBytes) > 0;
#endif
}