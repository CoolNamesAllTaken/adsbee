#include "spi_coprocessor.hh"

#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hal.hh"
#elif defined(ON_ESP32)
#include "adsbee_server.hh"

// Called after a transaction is queued and ready for pickup by master. We use this to set the handshake line high.
void IRAM_ATTR esp_spi_post_setup_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(1); }

// Called after transaction is sent/received. We use this to set the handshake line low.
void IRAM_ATTR esp_spi_post_trans_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(0); }

#endif

bool SPICoprocessor::Init() {
#ifdef ON_PICO
    if (config_.init_callback) {
        config_.init_callback();
    }

#elif defined(ON_ESP32)
    gpio_set_direction(config_.network_led_pin, GPIO_MODE_OUTPUT);
    spi_bus_config_t spi_buscfg = {.mosi_io_num = config_.spi_mosi_pin,
                                   .miso_io_num = config_.spi_miso_pin,
                                   .sclk_io_num = config_.spi_clk_pin,
                                   .data2_io_num = -1,  // union with quadwp_io_num
                                   .data3_io_num = -1,  // union with quadhd_io_num
                                   .data4_io_num = -1,
                                   .data5_io_num = -1,
                                   .data6_io_num = -1,
                                   .data7_io_num = -1,
                                   .data_io_default_level = false,  // keep lines LO when not in use
                                   .max_transfer_sz = SPICoprocessor::kSPITransactionMaxLenBytes,
                                   .flags = 0,
                                   .isr_cpu_id = ESP_INTR_CPU_AFFINITY_AUTO,
                                   .intr_flags = 0};
    spi_slave_interface_config_t spi_slvcfg = {.spics_io_num = config_.spi_cs_pin,
                                               .flags = 0,
                                               .queue_size = 3,
                                               .mode = 0,
                                               .post_setup_cb = esp_spi_post_setup_cb,
                                               .post_trans_cb = esp_spi_post_trans_cb};
    gpio_config_t handshake_io_conf = {
        .pin_bit_mask = (static_cast<uint64_t>(0b1) << config_.spi_handshake_pin),
        .mode = GPIO_MODE_OUTPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&handshake_io_conf);
    gpio_set_pull_mode(config_.spi_mosi_pin, GPIO_PULLDOWN_ONLY);
    gpio_set_pull_mode(config_.spi_miso_pin, GPIO_PULLDOWN_ONLY);
    gpio_set_pull_mode(config_.spi_clk_pin, GPIO_PULLDOWN_ONLY);
    gpio_set_pull_mode(config_.spi_cs_pin, GPIO_PULLUP_ONLY);

    // Adjust drive strength on MISO pin.
    gpio_set_drive_capability(config_.spi_miso_pin, GPIO_DRIVE_CAP_MAX);

    esp_err_t status = spi_slave_initialize(config_.spi_handle, &spi_buscfg, &spi_slvcfg, SPI_DMA_CH_AUTO);
    if (status != ESP_OK) {
        ESP_LOGE("SPICoprocessor::SPIInit", "SPI initialization failed with code 0x%x.", status);
        return false;
    }

    spi_mutex_ = xSemaphoreCreateMutex();
    spi_next_transaction_mutex_ = xSemaphoreCreateMutex();
#endif
    return true;
}

bool SPICoprocessor::DeInit() {
#ifdef ON_PICO
    if (config_.deinit_callback) {
        config_.deinit_callback();
    }

    // Don't deinit pins or SPI peripheral since some are shared by other peripherals.

#elif defined(ON_ESP32)
    spi_receive_task_should_exit_ = true;
#endif
    return true;
}

bool SPICoprocessor::Update(bool blocking) {
    bool ret = false;
#ifdef ON_PICO
    // Do a blocking check of the HANDSHAKE pin to make sure that the ESP32 can have its say.
    if (!GetSPIHandshakePinLevel(blocking)) {
        return true;  // Nothing to do.
    }

    // Incoming unsolicited transmission from ESP32.
    uint8_t rx_buf[kSPITransactionMaxLenBytes];
    SPIReadBlocking(rx_buf, 1, false);  // Peek the command first, keep chip select asserted.
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
            ret =
                object_dictionary.SetBytes(write_packet.addr, write_packet.data, write_packet.len, write_packet.offset);
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
            SPIReadBlocking(rx_buf + sizeof(SCCommand), SCReadRequestPacket::kBufLenBytes - sizeof(SCCommand), false);
            SCReadRequestPacket read_request_packet = SCReadRequestPacket(rx_buf, SCReadRequestPacket::kBufLenBytes);
            if (!read_request_packet.IsValid()) {
                SPIEndTransaction();
                CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited read from master with bad checksum.");
                return false;
            }
            SCResponsePacket response_packet;
            response_packet.cmd = kCmdDataBlock;
            ret = object_dictionary.GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
                                             read_request_packet.offset);
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
            SPIEndTransaction();
            CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited packet from ESP32 with unsupported cmd=%d.",
                          cmd);
            return false;
    }
#elif defined(ON_ESP32)
    uint8_t rx_buf[kSPITransactionMaxLenBytes];
    memset(rx_buf, 0, kSPITransactionMaxLenBytes);

    if (xSemaphoreTake(spi_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
        CONSOLE_ERROR("SPICoprocessor::SPIWriteReadBlocking",
                      "Failed to acquire coprocessor SPI mutex after waiting %d ms.", kSPITransactionTimeoutMs);
        return false;
    }

    use_handshake_pin_ = false;  // Don't solicit a transfer.
    int16_t bytes_read = SPIReadBlocking(rx_buf);
    if (bytes_read < 0) {
        if (bytes_read != kErrorTimeout) {
            CONSOLE_ERROR("SPICoprocessor::Update", "SPI read received non-timeout error code 0x%x.", bytes_read);
            return SPISlaveLoopReturnHelper(false);
        }
        return SPISlaveLoopReturnHelper(true);  // Timeout errors are OK and expected.
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
                return SPISlaveLoopReturnHelper(false);
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
                return SPISlaveLoopReturnHelper(false);
            }

            SCResponsePacket response_packet;
            response_packet.cmd = kCmdDataBlock;
            ret = object_dictionary.GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
                                             read_request_packet.offset);
            if (!ret) {
                CONSOLE_ERROR("SPICoprocessor::Update",
                              "Failed to retrieve data for %d Byte read from slave at address 0x%x",
                              read_request_packet.len, read_request_packet.addr);
            }
            response_packet.data_len_bytes = read_request_packet.len;  // Assume the correct number of bytes were read.
            response_packet.PopulateCRC();
            use_handshake_pin_ = true;  // Solicit a read from the RP2040.
            SPIWriteBlocking(response_packet.GetBuf(), response_packet.GetBufLenBytes());
            break;
        }
        default:
            CONSOLE_ERROR("SPICoprocessor::Update",
                          "Received unsolicited packet from RP2040 with unsupported cmd=%d, packet length %d Bytes.",
                          cmd, bytes_read);
            return SPISlaveLoopReturnHelper(false);
    }

#endif

    return SPISlaveLoopReturnHelper(ret);
}

#ifdef ON_PICO
bool SPICoprocessor::GetSPIHandshakePinLevel(bool blocking) {
    if (blocking) {
        // Blocking wait before pre-assert interval.
        while (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ <
               kSPIMinTransmitIntervalUs - kSPIUpdateCSPreAssertIntervalUs) {
            // Check for Handshake pin going high after post transmit lockout period.
            if (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ > kSPIPostTransmitLockoutUs &&
                gpio_get(config_.spi_handshake_pin)) {
                // Allowed to exit blocking early if ESP32 asserts the HANDSHAKE pin.
                volatile bool early_exit = true;  // Just for debugging, allows breakpoint here.
                return true;
            }
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

bool SPICoprocessor::SPIWaitForHandshake() {
    uint32_t wait_begin_timestamp_ms = get_time_since_boot_ms();
    while (true) {
        if (gpio_get(config_.spi_handshake_pin)) {
            break;
        }
        if (get_time_since_boot_ms() - wait_begin_timestamp_ms >= kSPIHandshakeTimeoutMs) {
            return false;
        }
    }
    return true;
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
    use_handshake_pin_ = true;  // Solicit a transfer to send the ack.
#endif
    return SPIWriteBlocking(response_packet.GetBuf(), SCResponsePacket::kAckLenBytes) > 0;
}

bool SPICoprocessor::SPIWaitForAck() {
    SCResponsePacket response_packet;
#ifdef ON_PICO
    if (!SPIWaitForHandshake()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Timed out while waiting for ack: never received handshake.");
        return false;
    }
#elif defined(ON_ESP32)
    use_handshake_pin_ = false;  // Don't solicit an ack when waiting for one.
#endif
    int bytes_read = SPIReadBlocking(response_packet.GetBuf(), SCResponsePacket::kAckLenBytes);
    response_packet.data_len_bytes = SCResponsePacket::kAckLenBytes;
    if (response_packet.cmd != kCmdAck) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck",
                      "Received a message that was not an ack (cmd=0x%x, expected 0x%x).", response_packet.cmd,
                      kCmdAck);
        return false;
    }
    if (bytes_read < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "SPI read failed with code 0x%x.", bytes_read);
        return false;
    }
    if (!response_packet.IsValid()) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Received a response packet with an invalid CRC.");
        return false;
    }
    return response_packet.data[0];  // Return ACK / NACK value.
}

int SPICoprocessor::SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes, bool end_transaction) {
    int bytes_written = 0;
#ifdef ON_PICO

    // Wait for the next transmit interval (blocking) so that we don't overwhelm the slave with messages.
    while (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ < kSPIMinTransmitIntervalUs) {
        if (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ > kSPIPostTransmitLockoutUs &&
            gpio_get(config_.spi_handshake_pin)) {
            // Slave is requesting another write, and we're convinced it's properly processed the previous transaction.
            break;
        }
    }

    SPIBeginTransaction();
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
        CONSOLE_ERROR("SPICoprocessor::SPIWriteReadBlocking", "SPI write read call returned error code 0x%x.",
                      bytes_written);
    }
#elif defined(ON_ESP32)
    spi_slave_transaction_t t;
    memset(&t, 0, sizeof(t));

    t.length = len_bytes * kBitsPerByte;  // Transaction length is in bits
    t.tx_buffer = tx_buf == nullptr ? nullptr : spi_tx_buf_;
    t.rx_buffer = rx_buf == nullptr ? nullptr : spi_rx_buf_;

    if (tx_buf != nullptr) {
        memcpy(spi_tx_buf_, tx_buf, len_bytes);
    }

    /** Send a write packet from slave -> master via handshake. **/
    // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received until max
    // delay. Currently, setting the delay here to anything other than portMAX_DELAY (which allows blocking
    // indefinitely) causes an error in spi_slave.c due to extra transactions getting stuck in the SPI peripheral queue.
    esp_err_t status = spi_slave_transmit(config_.spi_handle, &t, portMAX_DELAY /*kSPITransactionTimeoutTicks*/);

    if (status != ESP_OK) {
        if (status == ESP_ERR_TIMEOUT) {
            return kErrorTimeout;  // Timeouts fail silently.
        }
        CONSOLE_ERROR("SPICoprocesor::SPIWriteReadBlocking", "SPI transaction failed unexpectedly with code 0x%x.",
                      status);
        return kErrorGeneric;
    }
    bytes_written = CeilBitsToBytes(t.trans_len);
    if (rx_buf != nullptr) {
        memcpy(rx_buf, spi_rx_buf_, len_bytes);
    }
#endif
    return bytes_written;
}

bool SPICoprocessor::PartialWrite(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset,
                                  bool require_ack) {
    SCWritePacket write_packet;
#ifdef ON_PICO
    write_packet.cmd = require_ack ? kCmdWriteToSlaveRequireAck : kCmdWriteToSlave;
#elif defined(ON_ESP32)
    write_packet.cmd = require_ack ? kCmdWriteToMasterRequireAck : kCmdWriteToMaster;
#else
    return false;  // Not supported on other platforms.
#endif
    write_packet.addr = addr;
    memcpy(write_packet.data, object_buf + offset, len);
    write_packet.len = len;
    write_packet.offset = offset;
    write_packet.PopulateCRC();

#ifdef ON_ESP32
    if (xSemaphoreTake(spi_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
        CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Failed to acquire coprocessor SPI mutex after waiting %d ms.",
                      kSPIMutexTimeoutMs);
        return false;
    }
#endif
    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
#ifdef ON_PICO
        // Call Update with blocking to flush ESP32 of messages before write (block to make sure it has a chance to
        // talk if it needs to).
        Update(true);  // Check to see if handshake line is raised before blasting a packet into the ESP32.
#elif defined(ON_ESP32)
        // Handshake pin gets set LO by SPIWaitForAck(), so we need to re-assert it here for retries to bring it HI.
        use_handshake_pin_ = true;  // Set handshake pin to solicit a transaction with the RP2040.
#endif
        int bytes_written = SPIWriteBlocking(write_packet.GetBuf(), write_packet.GetBufLenBytes());

        if (bytes_written < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d while writing object over SPI.", bytes_written);
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
#ifdef ON_ESP32
    xSemaphoreGive(spi_mutex_);  // Allow other tasks to access the SPI peripheral.
#endif
    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Failed after %d tries: %s", num_attempts, error_message);
    }
    return ret;
}

bool SPICoprocessor::PartialRead(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset) {
    SCReadRequestPacket read_request_packet;
#ifdef ON_PICO
    read_request_packet.cmd = kCmdReadFromSlave;
#elif defined(ON_ESP32)
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

#ifdef ON_ESP32
    if (xSemaphoreTake(spi_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
        CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed to acquire coprocessor SPI mutex after waiting %d ms.",
                      kSPIMutexTimeoutMs);
        return false;
    }
#endif

    int num_attempts = 0;
    char error_message[kErrorMessageMaxLen + 1] = "No error.";
    error_message[kErrorMessageMaxLen] = '\0';
    bool ret = true;
    while (num_attempts < kSPITransactionMaxNumRetries) {
#ifdef ON_PICO
        // On the master, reading from the slave is two transactions: The read request is sent, then we wait on the
        // handshake line to read the reply.
        SCResponsePacket response_packet;  // Declare this up here so the goto's don't cross it.
        // Call Update with blocking to flush ESP32 of messages before write (block to make sure it has a chance to
        // talk
        // if it needs to).
        Update(true);  // Check to see if handshake line is raised before blasting a packet into the ESP32.
        int bytes_written = SPIWriteBlocking(read_request_packet.GetBuf(), read_request_bytes);
        int bytes_read = 0;
        if (bytes_written < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d while writing read request over SPI.",
                     bytes_written);
            goto PARTIAL_READ_FAILED;
        }
        if (!SPIWaitForHandshake()) {
            snprintf(error_message, kErrorMessageMaxLen,
                     "Timed out while waiting for handshake after sending read request.");
            goto PARTIAL_READ_FAILED;
        }

        response_packet.data_len_bytes =
            len;  // We need to set this manually since we are using the default constructor.
        bytes_read = SPIReadBlocking(response_packet.GetBuf(), SCResponsePacket::GetBufLenForPayloadLenBytes(len));
        if (bytes_read < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d while reading read response over SPI.",
                     bytes_read);
            goto PARTIAL_READ_FAILED;
        }
#elif defined(ON_ESP32)
        // On the slave, reading from the master is a single transaction. We preload the beginning of the message
        // with the read request, and the master populates the remainder of the message with the reply.
        use_handshake_pin_ = true;  // Set handshake pin to solicit a transaction with the RP2040.
        // Need to request the max transaction size. If we request something smaller, like read_request_bytes (which
        // doesn't include the response bytes), the SPI transmit function won't write the additional reply into our
        // buffer.
        int bytes_exchanged = SPIWriteReadBlocking(read_request_packet.GetBuf(), rx_buf, SCPacket::kPacketMaxLenBytes);

        if (bytes_exchanged < 0) {
            snprintf(error_message, kErrorMessageMaxLen, "Error code %d during read from master SPI transaction.",
                     bytes_exchanged);
            // Can't use the goto shortcut here because it would cross over response_packet initialization.
            CONSOLE_WARNING("SPICoprocessor::PartialRead", "%s", error_message);
            num_attempts++;
            ret = false;
            // Mutex can be given back immediately because we don't ever wait for an ACK.
            xSemaphoreGive(spi_mutex_);  // Allow other tasks to access the SPI peripheral.
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
            xSemaphoreGive(spi_mutex_);  // Allow other tasks to access the SPI peripheral.
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
#ifdef ON_ESP32
    xSemaphoreGive(spi_mutex_);  // Allow other tasks to access the SPI peripheral.
#endif
    if (!ret) {
        CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed after %d tries: %s", num_attempts, error_message);
    }
    return ret;
}