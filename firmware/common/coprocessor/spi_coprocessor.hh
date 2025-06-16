#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "aircraft_dictionary.hh"
#include "comms.hh"
#include "hal.hh"
#include "macros.hh"
#include "object_dictionary.hh"
#include "settings.hh"
#include "transponder_packet.hh"

#ifdef ON_PICO
#include <functional>  // For std::function.

#include "bsp.hh"
#include "hardware/gpio.h"
#include "hardware/spi.h"
#elif defined(ON_ESP32)
#include "data_structures.hh"
#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#endif

class SPICoprocessor {
   public:
    static constexpr uint16_t kSPITransactionMaxLenBytes =
        4096;  // Default max is 4096 Bytes on ESP32 (with DMA) and 4096 Bytes on RP2040.
    static_assert(kSPITransactionMaxLenBytes % 4 == 0);  // Make sure it's word-aligned.
    static constexpr uint16_t kSPITransactionQueueLenTransactions = 3;
    static constexpr uint16_t kSPITransactionMaxNumRetries =
        3;  // Max num retries per block in a multi-transfer transaction.

#ifdef ON_PICO
    // Make sure that we don't talk to the slave before it has a chance to get ready for the next message.
    // Note that this value is ignored if the HANDSHAKE line is pulled high.
    static constexpr uint32_t kSPIMinTransmitIntervalUs = 600;
    // Wait this long after a transmission is complete before allowing the HANDSHAKE line to override the minimum
    // transmit interval timeout. This ensures that we don't double-transmit to the slave before it has a chance to
    // lower the HANDSHAKE line following a transaction.
    static constexpr uint32_t kSPIPostTransmitLockoutUs = 10;
    // How long before the end of kSPIMinTransmitIntervalUs to assert the CS line during a blocking update. This
    // prevents the ESP32 from handshaking at the same instant that the Pico starts a transaction with the assumption
    // that the Hanshake line was LO.
    static constexpr uint32_t kSPIUpdateCSPreAssertIntervalUs = 100;
    // NOTE: Max transmission time is ~10ms with a 4kB packet at 40MHz.
    // How long to wait once a transaction is started before timing out.
    static constexpr uint16_t kSPITransactionTimeoutMs = 20;
    // How long a blocking wait for a handshake can last.
    static constexpr uint16_t kSPIHandshakeTimeoutMs = 20;
#elif defined(ON_ESP32)
    static constexpr uint32_t kNetworkLEDBlinkDurationMs = 10;
    static constexpr uint32_t kNetworkLEDBlinkDurationTicks = kNetworkLEDBlinkDurationMs / portTICK_PERIOD_MS;
    // Since the transaction timeout value is used by threads waiting to use the SPI peripheral, and the SPI update task
    // blocks the copro_spi_mutex_ until it receives a transfer from the master, this timeout needs to be set to the
    // maximum delay between unsolicited packets from the master (heartbeat) to avoid threads giving up while the SPI
    // update task is hogging the mutex.
    // How long to wait once a transaction is started before timing out.
    static constexpr uint16_t kSPITransactionTimeoutMs = 200;
    static constexpr uint16_t kSPITransactionTimeoutTicks = kSPITransactionTimeoutMs / portTICK_PERIOD_MS;
    static constexpr uint16_t kSPIMutexTimeoutMs =
        1200;  // How long to wait for the transaction mutex before timing out.
    static constexpr uint16_t kSPIMutexTimeoutTicks = kSPIMutexTimeoutMs / portTICK_PERIOD_MS;
#endif
    struct SPICoprocessorConfig {
#ifdef ON_PICO
        spi_inst_t *spi_handle = bsp.copro_spi_handle;
        uint16_t spi_cs_pin = UINT16_MAX;  // Pin for SPI chip select (CS).
        uint16_t spi_handshake_pin = UINT16_MAX;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;

        // Callback allow functionality to be overridden for different underlying devices.
        std::function<bool()> init_callback = nullptr;
        std::function<bool()> deinit_callback = nullptr;
        std::function<bool()> is_enabled_callback = nullptr;
        std::function<void(bool)> set_enable_callback = nullptr;
        std::function<void()> spi_begin_transaction_callback = nullptr;
        std::function<void()> spi_end_transaction_callback = nullptr;
#elif defined(ON_ESP32)
        spi_host_device_t spi_handle = SPI2_HOST;
        gpio_num_t spi_mosi_pin = GPIO_NUM_41;
        gpio_num_t spi_miso_pin = GPIO_NUM_42;
        gpio_num_t spi_clk_pin = GPIO_NUM_40;
        gpio_num_t spi_cs_pin = GPIO_NUM_39;
        gpio_num_t spi_handshake_pin = GPIO_NUM_0;

        gpio_num_t network_led_pin = GPIO_NUM_5;
#endif
    };

    /** NOTE: Packets should not be used outside of the SPICoprocessor class, they are only exposed for testing. **/

    // Commands are written from Master to Slave.
    enum SCCommand : uint8_t {
        kCmdInvalid = 0x00,
        kCmdWriteToSlave = 0x01,            // No response expected.
        kCmdWriteToSlaveRequireAck = 0x02,  // Expects a response to continue to the next block.
        kCmdReadFromSlave = 0x03,
        kCmdWriteToMaster = 0x04,            // No response expected.
        kCmdWriteToMasterRequireAck = 0x05,  // Expects a response to continue to the next block.
        kCmdReadFromMaster = 0x06,
        kCmdDataBlock = 0x07,
        kCmdAck = 0x08
    };
    /**
     * Abstract base struct for SPI Coprocessor packets.
     */
    struct __attribute__((__packed__)) SCPacket {
        static constexpr uint16_t kPacketMaxLenBytes = kSPITransactionMaxLenBytes;
        static constexpr uint16_t kCRCLenBytes = sizeof(uint16_t);

        // Pure virtual functions.
        virtual inline uint16_t GetBufLenBytes() = 0;
        // GetBuf needs to return the beginning of the elements of the child class, not "this", since "this" points to
        // the beginning of the child class struct, which first contains a pointer to this virtual base class.
        virtual inline uint8_t *GetBuf() = 0;
        virtual inline uint8_t *GetCRCPtr() = 0;

        // Virtual functions.
        virtual inline bool IsValid() { return CalculateCRC16(GetBuf(), GetBufLenBytes() - kCRCLenBytes) == GetCRC(); }
        virtual inline void PopulateCRC() { SetCRC(CalculateCRC16(GetBuf(), GetBufLenBytes() - kCRCLenBytes)); }
        virtual inline uint16_t GetCRC() {
            uint16_t crc_out = 0x0;
            // Extract CRC safely regardless of memory alignment.
            memcpy(&crc_out, GetCRCPtr(), sizeof(uint16_t));
            return crc_out;
        }
        virtual inline void SetCRC(uint16_t crc_in) {
            // Set CRC safely regardless of memory alignment.
            memcpy(GetCRCPtr(), &crc_in, sizeof(uint16_t));
        }
    };

    /**
     * SPI Coprocessor Write Packet
     *
     * Used to write to slave (from master), or write to master (from slave). Does not receive a reply.
     */
    struct __attribute__((__packed__)) SCWritePacket : public SCPacket {
        static constexpr uint16_t kDataOffsetBytes =
            sizeof(SCCommand) + sizeof(ObjectDictionary::Address) + sizeof(uint16_t) + sizeof(uint16_t);
        static constexpr uint16_t kDataMaxLenBytes = kPacketMaxLenBytes - kDataOffsetBytes - kCRCLenBytes;
        static constexpr uint16_t kBufMinLenBytes = kDataOffsetBytes + kCRCLenBytes;

        /** Begin packet contents on the wire. **/
        SCCommand cmd = kCmdInvalid;
        ObjectDictionary::Address addr = ObjectDictionary::kAddrInvalid;
        uint16_t offset = 0;
        uint16_t len = 0;                               // Length from start of data to beginning of CRC.
        uint8_t data[kDataMaxLenBytes + kCRCLenBytes];  // CRC is secretly appended at the end of data so that the
                                                        // struct can be used as a buffer to send with.
        /** End packet contents on the wire. **/

        /**
         * Default constructor.
         */
        SCWritePacket() { memset(data, 0x0, kDataMaxLenBytes); }

        /**
         * Constructor from buffer. Used for creating an SCCommand packet from a SPI transaction.
         * @param[in] buf_in Pointer to buffer with SCCommand packet in it.
         * @param[in] buf_in_len_bytes Length of the buffer to ingest.
         */
        SCWritePacket(uint8_t *buf_in, uint16_t buf_in_len_bytes) {
            if (buf_in_len_bytes < kBufMinLenBytes) {
                CONSOLE_ERROR("SPICoprocessor::SCWritePacket",
                              "Attempted to create a packet from a buffer that was too small. Received %d bytes, but"
                              "needed at least %d!",
                              buf_in_len_bytes, kBufMinLenBytes);
                return;
            }
            memcpy(GetBuf(), buf_in, buf_in_len_bytes);
            // Override the len field that we read in since it's important for calculating CRC.
            len = buf_in_len_bytes - kDataOffsetBytes - kCRCLenBytes;
        }

        inline uint16_t GetBufLenBytes() override { return kDataOffsetBytes + len + kCRCLenBytes; }
        inline uint8_t *GetBuf() override { return (uint8_t *)(&cmd); }
        inline uint8_t *GetCRCPtr() override { return data + MIN(len, kDataMaxLenBytes); }
    };

    /**
     * SPI Coprocessor Read Request Packet
     *
     * Used to request a read from slave (by master) or request a read from master (by slave). Receives a
     * SCResponsePacket in response.
     */
    struct __attribute__((__packed__)) SCReadRequestPacket : public SCPacket {
        static constexpr uint16_t kBufLenBytes =
            sizeof(SCCommand) + sizeof(ObjectDictionary::Address) + 2 * sizeof(uint16_t) + kCRCLenBytes;
        /** Begin packet contents on the wire. **/
        SCCommand cmd = kCmdInvalid;
        ObjectDictionary::Address addr = ObjectDictionary::kAddrInvalid;
        uint16_t offset = 0;
        uint16_t len = 0;
        uint16_t crc;
        /** End packet contents on the wire. **/

        /**
         * Default constructor.
         */
        SCReadRequestPacket() {}

        /**
         * Constructor from buffer. Used for creating an SCReadRequest packet from a SPI transaction.
         * @param[in] buf_in Pointer to buffer with SCReadRequest packet in it.
         * @param[in] buf_in_len_bytes Length of the buffer to ingest.
         */
        SCReadRequestPacket(uint8_t *buf_in, uint16_t buf_in_len_bytes) {
            if (buf_in_len_bytes < kBufLenBytes) {
                CONSOLE_ERROR(
                    "SPICoprocessor::SCReadRequestPacket",
                    "Attempted to create a packet from a buffer that was too small. Received %d Bytes, but needed %d!",
                    buf_in_len_bytes, kBufLenBytes);
                return;
            }
            memcpy(GetBuf(), buf_in, buf_in_len_bytes);
        }

        inline uint16_t GetCRC() override { return crc; }
        inline void SetCRC(uint16_t crc_in) override { crc = crc_in; }
        inline uint16_t GetBufLenBytes() override { return kBufLenBytes; }
        inline uint8_t *GetBuf() override { return (uint8_t *)(&cmd); }
        inline uint8_t *GetCRCPtr() override { return (uint8_t *)&crc; }
    };

    /**
     * SPI Coprocessor Response Packet
     *
     * Response to a Read Request Packet, containing the requested data, or response to a Write Request Packet Requiring
     * Ack, containing an ack.
     */
    struct __attribute__((__packed__)) SCResponsePacket : public SCPacket {
        static constexpr uint16_t kDataMaxLenBytes = kPacketMaxLenBytes - sizeof(SCCommand) - kCRCLenBytes;
        static constexpr uint16_t kDataOffsetBytes = sizeof(SCCommand);
        static constexpr uint16_t kBufMinLenBytes = sizeof(SCCommand) + kCRCLenBytes;  // No payload Bytes.

        // ACK packet is special format of SCResponse packet with a single byte data payload.
        // ACK format: CMD | ACK | CRC
        // ADDR = kCmdAck
        // ACK = true if success, false if fail
        // CRC = CRC16
        static constexpr uint16_t kAckLenBytes = sizeof(SCCommand) + 1 + kCRCLenBytes;

        /**
         * Convenience function that tells you how long a response packet would be with a payload of X bytes.
         * @param[in] payload_len_bytes Payload length in Bytes.
         * @retval Buffer length in Bytes for an SCResponsePacket containing the given payload.
         */
        static inline uint16_t GetBufLenForPayloadLenBytes(uint16_t payload_len_bytes) {
            return kDataOffsetBytes + payload_len_bytes + kCRCLenBytes;
        }

        /** Begin packet contents on the wire. **/
        SCCommand cmd = kCmdInvalid;
        uint8_t data[kDataMaxLenBytes + kCRCLenBytes];
        /** End packet contents on the wire. **/

        uint16_t data_len_bytes = 0;  // Length from start of data to beginning of CRC.

        /**
         * Default constructor.
         */
        SCResponsePacket() { memset(data, 0x0, kDataMaxLenBytes); }

        /**
         * Constructor from buffer. Used for creating an SCReadResponse packet from a SPI transaction.
         * @param[in] buf_in Pointer to buffer with SCReadResponse packet in it.
         * @param[in] buf_in_len_bytes Length of the buffer to ingest.
         */
        SCResponsePacket(uint8_t *buf_in, uint16_t buf_in_len_bytes) {
            if (buf_in_len_bytes < kBufMinLenBytes) {
                CONSOLE_ERROR("SPICoprocessor::SCResponsePacket",
                              "Attempted to create a packet from a buffer that was too small. Received %d Bytes, but "
                              "needed at least %d!",
                              buf_in_len_bytes, kBufMinLenBytes);
                return;
            }
            memcpy(GetBuf(), buf_in, buf_in_len_bytes);
            data_len_bytes = buf_in_len_bytes - kDataOffsetBytes - kCRCLenBytes;
        }

        inline uint16_t GetBufLenBytes() override { return kDataOffsetBytes + data_len_bytes + kCRCLenBytes; }
        inline uint8_t *GetBuf() override { return (uint8_t *)(&cmd); }
        inline uint8_t *GetCRCPtr() override { return data + data_len_bytes; }
    };

    /**
     * Constructor
     */
    SPICoprocessor(SPICoprocessorConfig config_in) : config_(config_in) {
#ifdef ON_PICO
        // Make sure that override functions and values are defined.
        assert(config_.spi_handle);
        assert(config_.spi_cs_pin != UINT16_MAX);
        assert(config_.spi_handshake_pin != UINT16_MAX);
        assert(config_.is_enabled_callback);
        assert(config_.set_enable_callback);

        // Init and deinit callbacks are optional.
#elif defined(ON_ESP32)
        spi_rx_buf_ = static_cast<uint8_t *>(heap_caps_malloc(kSPITransactionMaxLenBytes, MALLOC_CAP_DMA));
        spi_tx_buf_ = static_cast<uint8_t *>(heap_caps_malloc(kSPITransactionMaxLenBytes, MALLOC_CAP_DMA));

        if (!spi_rx_buf_ || !spi_tx_buf_) {
            CONSOLE_ERROR("SPICoprocessor::SPICoprocessor", "Failed to allocate SPI tx/rx buffers.");
        }
        memset(spi_rx_buf_, 0x0, kSPITransactionMaxLenBytes);
        memset(spi_tx_buf_, 0x0, kSPITransactionMaxLenBytes);
#endif
    };

    /**
     * Destructor
     */
    ~SPICoprocessor() {
#ifdef ON_ESP32
        heap_caps_free(spi_rx_buf_);
        heap_caps_free(spi_tx_buf_);
#endif
    }

    bool Init();
    bool DeInit();
#ifdef ON_PICO
    bool IsEnabled() { return config_.is_enabled_callback(); }
    void SetEnable(bool enabled) { config_.set_enable_callback(enabled); }
#endif
    /**
     *
     * @param[in] blocking On RP2040, blocks until kSPIMinTransactionIntervalUs after the previous transaction to check
     * to see if the ESP32 has anything to say. Set to true if using this as a way to flush the ESP32 of messages before
     * writing to it. On ESP32, has no effect.
     */
    bool Update(bool blocking = false);

    /**
     * Top level function that translates a write to an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     */
    template <typename T>
    bool Write(ObjectDictionary::Address addr, T &object, bool require_ack = false, uint16_t len_bytes = 0) {
        if (len_bytes == 0) {
            len_bytes = sizeof(object);
        }
#ifdef ON_ESP32
        if (xSemaphoreTake(spi_next_transaction_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
            CONSOLE_ERROR("SPICoprocessor::Write", "Failed to take SPI context mutex after waiting for %d ms.",
                          kSPIMutexTimeoutMs);
            return false;
        }
#elif ON_PICO

#else
        return false;  // Not supported on other platforms.
#endif
        if (len_bytes < SCWritePacket::kDataMaxLenBytes) {
            // Single write. Write the full object at once, no offset, require ack if necessary.
            return SPIIndependentLoopReturnHelper(PartialWrite(addr, (uint8_t *)&object, len_bytes, 0, require_ack));
        } else {
            // Multi write.
            int16_t bytes_remaining = len_bytes;
            while (bytes_remaining > 0) {
                if (!PartialWrite(addr,                                                   // addr
                                  (uint8_t *)(&object),                                   // object
                                  MIN(SCWritePacket::kDataMaxLenBytes, bytes_remaining),  // len
                                  len_bytes - bytes_remaining,                            // offset
                                  require_ack)                                            // require_ack
                ) {
                    CONSOLE_ERROR(
                        "SPICoprocessor::Write",
                        "Multi-transfer %d Byte write of object at address 0x%x failed with %d Bytes remaining.",
                        len_bytes, addr, bytes_remaining);
                    return SPIIndependentLoopReturnHelper(false);
                }
                bytes_remaining -= SCWritePacket::kDataMaxLenBytes;
            }
            return SPIIndependentLoopReturnHelper(true);
        }
        return SPIIndependentLoopReturnHelper(false);
    }

    /**
     * Top level function that translates a read from an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     */
    template <typename T>
    bool Read(ObjectDictionary::Address addr, T &object, uint16_t len_bytes = 0) {
        if (len_bytes == 0) {
            len_bytes = sizeof(object);
        }
#ifdef ON_PICO
#elif defined(ON_ESP32)
        if (xSemaphoreTake(spi_next_transaction_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
            CONSOLE_ERROR("SPICoprocessor::PartialRead", "Failed to take SPI context mutex after waiting for %d ms.",
                          kSPIMutexTimeoutMs);
            return false;
        }
#elif defined(ON_TI)
#else
        return false;  // Not supported on other platforms.
#endif
        if (len_bytes < SCResponsePacket::kDataMaxLenBytes) {
            // Single read.
            return SPIIndependentLoopReturnHelper(PartialRead(addr, (uint8_t *)&object, len_bytes));

        } else {
            // Multi-read.
#ifdef ON_PICO
            // Write and read are separate transactions.
            uint16_t max_chunk_size_bytes = SCResponsePacket::kDataMaxLenBytes;
#elif defined(ON_ESP32) || defined(ON_TI)
            // Write and read are a single transaction.
            uint16_t max_chunk_size_bytes = SCResponsePacket::kDataMaxLenBytes - SCReadRequestPacket::kBufLenBytes;
#else
            uint16_t max_chunk_size_bytes = 0;  // Dummy to stop compile errors.
#endif
            int16_t bytes_remaining = len_bytes;
            while (bytes_remaining > 0) {
                if (!PartialRead(addr,                                        // address
                                 (uint8_t *)(&object),                        // object
                                 MIN(max_chunk_size_bytes, bytes_remaining),  // len
                                 len_bytes - bytes_remaining)                 // offset
                ) {
                    CONSOLE_ERROR(
                        "SPICoprocessor::Read",
                        "Multi-transfer %d Byte read of object at address 0x%x failed with %d Bytes remaining.",
                        len_bytes, addr, bytes_remaining);
                    return SPIIndependentLoopReturnHelper(false);
                }
                bytes_remaining -=
                    max_chunk_size_bytes;  // Overshoot on purpose on the last chunk. Bytes remaining will go negative.
            }
            return SPIIndependentLoopReturnHelper(true);
        }
        return SPIIndependentLoopReturnHelper(false);
    }

#ifndef ON_PICO
    /**
     * Log a message to the coprocessor. Not available on RP2040 since it's the master (other stuff logs to it).
     * @param[in] log_level Log level of the message.
     * @param[in] tag Tag to prepend to the message.
     * @param[in] format Format string for the message.
     * @param[in] ... Variable arguments for the format string.
     */
    bool LogMessage(SettingsManager::LogLevel log_level, const char *tag, const char *format, va_list args);
#endif

#ifdef ON_PICO
    /**
     * Checks the level of the HANDSHAKE pin used to initiate communication from the ESP32 to RP2040.
     * NOTE: There is some hysteresis! The ESP32 can request a transfer as soon as kSPIPostTransmitLockoutUs is up, but
     * this function won't unblock and confidently state that the HANDSHAKE pin is not asserted unless
     * kSPIMinTransmitIntervalUs has elapsed.
     * @param[in] blocking If true, wait until the pin is readable before reading it (e.g. it's been long enough since
     * the end of the last transaction that the ESP32 has been able to assert or de-assert the HANDSHAKE pin as
     * necessary). If false, return false if kSPIPostTransmitLockoutUs has not elapsed, otherwise return the HANDSHAKE
     * pin state.
     */
    bool GetSPIHandshakePinLevel(bool blocking = false);

    /**
     * Blocks on waiting for the handshake pin to go high, until a timeout is reached.
     * @retval True if handshake line went high before timeout, false otherwise.
     */
    bool SPIWaitForHandshake();
#elif defined(ON_ESP32)
    /**
     * Helper function used by callbacks to set the handshake pin high or low on the ESP32.
     * Located in IRAM for performance improvements when called from ISR.
     */
    inline void IRAM_ATTR SetSPIHandshakePinLevel(bool level) {
        // Only set the handshake pin HI when we know we want to solicit a response and not block + wait.
        // Handshake pin can always be set LO.
        gpio_set_level(config_.spi_handshake_pin, level && use_handshake_pin_);
    }

    /**
     * Function called from the task spawned during Init().
     */
    void SPIReceiveTask();

    /**
     * Turns on the network LED for a specified number of milliseconds. Relies on the UpdateNetowrkLED() function to
     * turn the lED off.
     * @param[in] blink_duration_ms Number of milliseconds that the LED should stay on for.
     */
    inline void BlinkNetworkLED(uint16_t blink_duration_ms = kNetworkLEDBlinkDurationMs) {
        gpio_set_level(config_.network_led_pin, 1);
        network_led_turn_on_timestamp_ticks_ = xTaskGetTickCount();
        network_led_on = true;
    }

    /**
     * Turns off the network LED if necessary.
     */
    inline void UpdateNetworkLED() {
        if (network_led_on &&
            xTaskGetTickCount() - network_led_turn_on_timestamp_ticks_ > kNetworkLEDBlinkDurationTicks) {
            gpio_set_level(config_.network_led_pin, 0);
            network_led_on = false;
        }
    }
#elif defined(ON_TI)
    /**
     * Helper function used by callbacks to set the handshake pin high or low on the CC1312.
     */
    inline void SetSPIHandshakePinLevel(bool level) {
        // Only set the handshake pin HI when we know we want to solicit a response and not block + wait.
        // Handshake pin can always be set LO.
        gpio_set_level(config_.spi_handshake_pin, level && use_handshake_pin_);
    }

    /**
     * Function called from the task spawned during Init().
     */
    void SPIReceiveTask();
#endif

   private:
    static constexpr uint16_t kErrorMessageMaxLen = 500;
    enum ReturnCode : int { kOk = 0, kErrorGeneric = -1, kErrorTimeout = -2 };

#ifdef ON_PICO
    void SPIBeginTransaction() {
        if (config_.spi_begin_transaction_callback) {
            // Use the overriden begin transaction callback for targets that need special settings changed.
            config_.spi_begin_transaction_callback();
        } else {
            gpio_put(config_.spi_cs_pin, 0);
        }
    }

    void SPIEndTransaction() {
        if (config_.spi_end_transaction_callback) {
            // Use the overriden end transaction callback for targets that need special settings changed.
            config_.spi_end_transaction_callback();
        } else {
            gpio_put(config_.spi_cs_pin, 1);
        }
        spi_last_transmit_timestamp_us_ = get_time_since_boot_us();
    }

#elif defined(ON_ESP32)
    SemaphoreHandle_t spi_mutex_;  // Low level mutex used to guard the SPI peripheral (don't let multiple
                                   // threads queue packets at the same time).
    SemaphoreHandle_t spi_next_transaction_mutex_;  // High level mutex used to claim the next transaction interval.
#elif defined(ON_TI)
#endif

    inline bool SPISlaveLoopReturnHelper(bool ret) {
#ifdef ON_ESP32
        xSemaphoreGive(spi_mutex_);  // Allow other tasks to access the SPI peripheral.

        // Trying to take the next transaction mutex in the slave loop (higher priority) temporarily boosts the priority
        // of other loops (e.g. lower priority independent update loop) if they have already claimed it. The next
        // transaction mutex is released before a SPI transmission so that it is available for other loops to claim
        // while the slave loop is blocking with no pending transactions.
        if (xSemaphoreTake(spi_next_transaction_mutex_, kSPIMutexTimeoutTicks) != pdTRUE) {
            CONSOLE_ERROR("SPICoprocessor::SPISlaveLoopReturnHelper",
                          "Other loops claiming the next SPI transaction didn't complete and return the next "
                          "transaction mutex within %d ms.",
                          kSPIMutexTimeoutMs);
        } else {
            xSemaphoreGive(spi_next_transaction_mutex_);
        }
        if (ret) {
            BlinkNetworkLED();
        }
#elif defined(ON_TI)
#endif
        return ret;
    }

    /**
     * Helper function that makes sure to return the next transaction mutex when returning from the indpendent loop (low
     * priority). Blinks the network LED to indicate a successful transaction.
     */
    inline bool SPIIndependentLoopReturnHelper(bool ret) {
#ifdef ON_ESP32
        xSemaphoreGive(spi_next_transaction_mutex_);
        if (ret) {
            BlinkNetworkLED();
        }
#elif defined(ON_TI)
#endif
        return ret;
    }

    bool PartialWrite(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset = 0,
                      bool require_ack = false);

    bool PartialRead(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset = 0);

    /**
     * Send an SCResponse packet with a single byte ACK payload.
     * @param[in] success True if sending an ACK, false if sending a NACK.
     * @retval True if ACK was transmitted successfully, false if something went wrong.
     */
    bool SPISendAck(bool success);

    /**
     * Blocks until an ACK is received or a timeout is reached.
     * @retval True if received an ACK, false if received NACK or timed out.
     */
    bool SPIWaitForAck();

    /**
     * Low level HAL for SPI Write Read call. Transmits the contents of tx_buf and receives into rx_buf.
     * Both buffers MUST be at least kSPITransactionMaxLenBytes Bytes long.
     * @param[in] tx_buf Buffer with data to transmit.
     * @param[in] rx_buf Buffer to fill with data that is received.
     * @param[in] len_bytes Number of bytes to transmit. Only has an effect when this function is being called on the
     * master.
     * @param[in] end_transaction Whether to de-assert chip select at the end of the transaction. Only has an effect
     * when this function is being called on the master.
     * @retval Number of bytes that were written and read, or a negative value if something broke.
     */
    int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                             bool end_transaction = true);

    // Write / Read aliases for SPIWriteReadBlocking.
    inline int SPIWriteBlocking(uint8_t *tx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                                bool end_transaction = true) {
        return SPIWriteReadBlocking(tx_buf, nullptr, len_bytes, end_transaction);
    }
    inline int SPIReadBlocking(uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                               bool end_transaction = true) {
        return SPIWriteReadBlocking(nullptr, rx_buf, len_bytes, end_transaction);
    }

    SPICoprocessorConfig config_;

#ifdef ON_PICO
    uint64_t spi_last_transmit_timestamp_us_ = 0;
#elif defined(ON_ESP32)
    // SPI peripheral needs to operate on special buffers that are 32-bit word aligned and in DMA accessible memory.
    uint8_t *spi_rx_buf_ = nullptr;
    uint8_t *spi_tx_buf_ = nullptr;

    bool spi_receive_task_should_exit_ = false;  // Flag used to tell SPI receive task to exit.
    TickType_t network_led_turn_on_timestamp_ticks_ = 0;
    bool network_led_on = false;
    bool use_handshake_pin_ =
        false;  // Allow handshake pin toggle to be skipped if waiting for a mesage and not writing to master.
#endif
};

#ifdef ON_PICO
extern SPICoprocessor esp32;
extern SPICoprocessor cc1312;
#elif defined(ON_ESP32) || defined(ON_TI)
extern SPICoprocessor pico;
#endif

#endif /* SPI_COPROCESSOR_HH_ */