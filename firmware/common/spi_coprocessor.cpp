#include "spi_coprocessor.hh"

#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hal.hh"
#include "hardware/gpio.h"
#elif ON_ESP32
#include "adsbee_server.hh"

// Called after a transaction is queued and ready for pickup by master. We use this to set the handshake line high.
void esp_spi_post_setup_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(1); }

// Called after transaction is sent/received. We use this to set the handshake line low.
void esp_spi_post_trans_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(0); }

#endif

bool SPICoprocessor::Init() {
#ifdef ON_PICO
    // ESP32 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // ESP32 handshake pin.
    gpio_init(config_.spi_handshake_pin);
    gpio_set_dir(config_.spi_handshake_pin, GPIO_IN);
    gpio_set_pulls(config_.spi_handshake_pin, true, false);  // Handshake pin is pulled up.
    // ESP32 SPI pins.
    gpio_set_function(config_.spi_clk_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_mosi_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_miso_pin, GPIO_FUNC_SPI);

    // Initialize SPI Peripheral.
    spi_init(config_.spi_handle, config_.clk_rate_hz);
    spi_set_format(config_.spi_handle,
                   8,           // Bits per transfer.
                   SPI_CPOL_0,  // Polarity (CPOL).
                   SPI_CPHA_0,  // Phase (CPHA).
                   SPI_MSB_FIRST);
#elif ON_ESP32
    gpio_set_direction(config_.network_led_pin, GPIO_MODE_OUTPUT);
    spi_bus_config_t spi_buscfg = {
        .mosi_io_num = config_.spi_mosi_pin,
        .miso_io_num = config_.spi_miso_pin,
        .sclk_io_num = config_.spi_clk_pin,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
    };
    spi_slave_interface_config_t spi_slvcfg = {.spics_io_num = config_.spi_cs_pin,
                                               .flags = 0,
                                               .queue_size = 3,
                                               .mode = 0,
                                               .post_setup_cb = esp_spi_post_setup_cb,
                                               .post_trans_cb = esp_spi_post_trans_cb};
    gpio_config_t handshake_io_conf = {
        .pin_bit_mask = (static_cast<uint64_t>(0b1) << config_.spi_handshake_pin),
        .mode = GPIO_MODE_OUTPUT,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&handshake_io_conf);
    gpio_set_pull_mode(config_.spi_mosi_pin, GPIO_PULLUP_ONLY);
    gpio_set_pull_mode(config_.spi_miso_pin, GPIO_PULLUP_ONLY);
    gpio_set_pull_mode(config_.spi_cs_pin, GPIO_PULLUP_ONLY);

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
    // ESP32 chip select pin.
    gpio_deinit(config_.spi_cs_pin);
    // ESP32 handshake pin.
    gpio_deinit(config_.spi_handshake_pin);

    // De-initialize SPI Peripheral.
    spi_deinit(config_.spi_handle);
#elif ON_ESP32
    spi_receive_task_should_exit_ = true;
#endif
    return true;
}

bool SPICoprocessor::Update() {
    bool ret = false;
#ifdef ON_PICO
    if (!GetSPIHandshakePinLevel()) {
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
            uint8_t len = rx_buf[SCWritePacket::kDataOffsetBytes - sizeof(uint8_t)];
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
            ret = SetBytes(write_packet.addr, write_packet.data, write_packet.len);
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
                gpio_put(config_.spi_cs_pin, true);  // Deselect slave when bailing out.
                CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited read from master with bad checksum.");
                return false;
            }
            SCResponsePacket response_packet;
            response_packet.cmd = kCmdDataBlock;
            ret = GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
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
            gpio_put(config_.spi_cs_pin, true);  // Deselect slave when bailing out.
            CONSOLE_ERROR("SPICoprocessor::Update", "Received unsolicited packet from ESP32 with unsupported cmd=%d.",
                          cmd);
            return false;
    }
#elif ON_ESP32
    uint8_t rx_buf[kSPITransactionMaxLenBytes];
    memset(rx_buf, 0, kSPITransactionMaxLenBytes);

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
            ret = SetBytes(write_packet.addr, write_packet.data, write_packet.len, write_packet.offset);
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
            ret = GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
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

/** Begin Private Functions **/

bool SPICoprocessor::SetBytes(SCAddr addr, uint8_t *buf, uint16_t buf_len, uint16_t offset) {
    switch (addr) {
        case kAddrScratch:
            memcpy((uint8_t *)&scratch_ + offset, buf, buf_len);
            break;
#ifdef ON_ESP32
        case kAddrRawTransponderPacket: {
            RawTransponderPacket tpacket = *(RawTransponderPacket *)buf;
            // CONSOLE_INFO("SPICoprocessor::SetBytes", "Received a raw %d-bit transponder packet.",
            //              tpacket.buffer_len_bits);
            adsbee_server.HandleRawTransponderPacket(tpacket);
            break;
        }
#endif
        case kAddrSettingsStruct:
            memcpy((uint8_t *)&(settings_manager.settings) + offset, buf, buf_len);
            break;
        default:
            CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for writing to address 0x%x.", addr);
            return false;
    }
    return true;
}

bool SPICoprocessor::GetBytes(SCAddr addr, uint8_t *buf, uint16_t buf_len, uint16_t offset) {
    switch (addr) {
        case kAddrScratch:
            memcpy(buf, (uint8_t *)(&scratch_) + offset, buf_len);
            break;
        case kAddrSettingsStruct:
            memcpy(buf, (uint8_t *)&(settings_manager.settings) + offset, buf_len);
            break;
        default:
            CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for reading from address 0x%x.", addr);
            return false;
    }
    return true;
}

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
#elif ON_ESP32
    use_handshake_pin_ = false;  // Don't solicit an ack when waiting for one.
#endif
    int bytes_read = SPIReadBlocking(response_packet.GetBuf(), SCResponsePacket::kAckLenBytes);
    response_packet.data_len_bytes = SCResponsePacket::kAckLenBytes;
    if (response_packet.cmd != kCmdAck) {
        CONSOLE_ERROR("SPICoprocessor::SPIWaitForAck", "Received a message that was not an ack.");
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
    }

    gpio_put(config_.spi_cs_pin, 0);
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
        gpio_put(config_.spi_cs_pin, 1);
    }
    if (bytes_written < 0) {
        CONSOLE_ERROR("SPICoprocessor::SPIWriteReadBlocking", "SPI write read call returned error code 0x%x.",
                      bytes_written);
    } else {
        // Only record the transmit time if the transaction was successful.
        spi_last_transmit_timestamp_us_ = get_time_since_boot_us();
    }
#elif ON_ESP32
    spi_slave_transaction_t t;
    memset(&t, 0, sizeof(t));

    t.length = len_bytes * kBitsPerByte;  // Transaction length is in bits
    t.tx_buffer = tx_buf;
    t.rx_buffer = rx_buf;

    /** Send a write packet from slave -> master via handshake. **/
    if (xSemaphoreTake(spi_mutex_, kSPITransactionTimeoutTicks) != pdTRUE) {
        CONSOLE_ERROR("SPICoprocessor::SPIWriteReadBlocking",
                      "Failed to acquire coprocessor SPI mutex after waiting %d ms.", kSPITransactionTimeoutMs);
        return kErrorTimeout;
    }
    // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received until max
    // delay. Currently, setting the delay here to anything other than portMAX_DELAY (which allows blocking
    // indefinitely) causes an error in spi_slave.c due to extra transactions getting stuck in the SPI peripheral queue.
    esp_err_t status = spi_slave_transmit(config_.spi_handle, &t, portMAX_DELAY /*kSPITransactionTimeoutTicks*/);
    xSemaphoreGive(spi_mutex_);

    if (status != ESP_OK) {
        if (status == ESP_ERR_TIMEOUT) {
            return kErrorTimeout;  // Timeouts fail silently.
        }
        CONSOLE_ERROR("SPICoprocesor::SPIWriteReadBlocking", "SPI transaction failed unexpectedly with code 0x%x.",
                      status);
        return kErrorGeneric;
    }
    bytes_written = CeilBitsToBytes(t.trans_len);
#endif
    return bytes_written;
}
