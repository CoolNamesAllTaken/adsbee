#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "aircraft_dictionary.hh"
#include "comms.hh"
#include "hal.hh"
#include "settings.hh"
#include "transponder_packet.hh"

#ifdef ON_PICO
#include "hardware/spi.h"
#elif ON_ESP32
#include "data_structures.hh"
#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#endif

class SPICoprocessor {
   public:
    static const uint16_t kSPITransactionMaxLenBytes = 64;
    static_assert(kSPITransactionMaxLenBytes % 4 == 0);  // Make sure it's word-aligned.
    static const uint16_t kSPITransactionQueueLenTransactions = 3;
    static const uint16_t kSPITransactionMaxNumRetries =
        3;  // Max num retries per block in a multi-transfer transaction.
    static const uint16_t kSPITransactionTimeoutMs = 100;

#ifdef ON_PICO
    static const uint16_t kHandshakePinMaxWaitDurationMs = 10;
#elif ON_ESP32
    static const uint32_t kNetworkLEDBlinkDurationMs = 10;
    static const uint32_t kNetworkLEDBlinkDurationTicks = kNetworkLEDBlinkDurationMs / portTICK_PERIOD_MS;
    static const uint16_t kSPITransactionTimeoutTicks = kSPITransactionTimeoutMs / portTICK_PERIOD_MS;
#endif
    struct SPICoprocessorConfig {
        uint32_t clk_rate_hz = 10e6;  // 40 MHz
#ifdef ON_PICO
        spi_inst_t *spi_handle = spi1;
        uint16_t spi_clk_pin = 10;
        uint16_t spi_mosi_pin = 11;
        uint16_t spi_miso_pin = 12;
        uint16_t spi_cs_pin = 9;
        uint16_t spi_handshake_pin = 13;
#elif ON_ESP32
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

    /** Begin edit these values for new packet types. **/

    enum SCAddr : uint8_t {
        kAddrInvalid = 0,           // Default value.
        kAddrScratch,               // Used for testing SPI communications.
        kAddrRawTransponderPacket,  // Used to forward raw packets from RP2040 to ESP32.
        kAddrSettingsStruct,        // Used to transfer settings information.
        kNumSCAddrs
    };

    /** End edit these values for new packet types. **/

    // Commands are written from Master to Slave.
    enum SCCommand : uint8_t {
        kCmdInvalid = 0x0,
        kCmdWriteToSlave,            // No response expected.
        kCmdWriteToSlaveRequireAck,  // Expects a response to continue to the next block.
        kCmdReadFromSlave,
        kCmdWriteToMaster,            // No response expected.
        kCmdWriteToMasterRequireAck,  // Expects a response to continue to the next block.
        kCmdReadFromMaster,
        kCmdDataBlock,
        kCmdAck
    };
    /**
     * Abstract base struct for SPI Coprocessor packets.
     */
    struct __attribute__((__packed__)) SCPacket {
        static const uint16_t kPacketMaxLenBytes = 64;
        static const uint16_t kCRCLenBytes = sizeof(uint16_t);

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
        static const uint16_t kDataOffsetBytes =
            sizeof(SCCommand) + sizeof(SCAddr) + sizeof(uint16_t) + sizeof(uint8_t);
        static const uint16_t kDataMaxLenBytes = kPacketMaxLenBytes - kDataOffsetBytes - kCRCLenBytes;
        static const uint16_t kBufMinLenBytes =
            sizeof(SCCommand) + sizeof(SCAddr) + sizeof(uint16_t) + sizeof(uint8_t) + kCRCLenBytes;

        /** Begin packet contents on the wire. **/
        SCCommand cmd = kCmdInvalid;
        SCAddr addr = kAddrInvalid;
        uint16_t offset = 0;
        uint8_t len = 0;                                // Length from start of data to beginning of CRC.
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
        inline uint8_t *GetCRCPtr() override { return data + len; }
    };

    /**
     * SPI Coprocessor Read Request Packet
     *
     * Used to request a read from slave (by master) or request a read from master (by slave). Receives a
     * SCReadReplyPacket in response.
     */
    struct __attribute__((__packed__)) SCReadRequestPacket : public SCPacket {
        static const uint16_t kBufLenBytes = sizeof(SCCommand) + sizeof(SCAddr) + 2 * sizeof(uint16_t) + kCRCLenBytes;
        /** Begin packet contents on the wire. **/
        SCCommand cmd = kCmdInvalid;
        SCAddr addr = kAddrInvalid;
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
        static const uint16_t kDataMaxLenBytes = kPacketMaxLenBytes - sizeof(SCCommand) - kCRCLenBytes;
        static const uint16_t kDataOffsetBytes = sizeof(SCCommand);
        static const uint16_t kBufMinLenBytes =
            sizeof(SCCommand) + 1 + kCRCLenBytes;  // Need at least one data Byte and CRC.

        // ACK packet is special format of SCResponse packet with a single byte data payload.
        // ACK format: CMD | ACK | CRC
        // ADDR = kCmdAck
        // ACK = true if success, false if fail
        // CRC = CRC16
        static const uint16_t kAckLenBytes = sizeof(SCCommand) + 1 + kCRCLenBytes;

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

    // NOTE: Pico (leader) and ESP32 (follower) will have different behaviors for these functions.
    bool Init();
    bool DeInit();
    bool Update();

    /**
     * Top level function that translates a write to an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     * Note that this function is not generally called directly, use the public Write and Read interfaces instead (no
     * address required).
     */
    template <typename T>
    bool Write(SCAddr addr, T &object, bool require_ack = false) {
        if (sizeof(object) < SCWritePacket::kDataMaxLenBytes) {
            // Single write. Write the full object at once, no offset, require ack if necessary.
            return PartialWrite(addr, (uint8_t *)&object, sizeof(object), 0, require_ack);
        } else {
            // Multi write.
            CONSOLE_ERROR("SPICoprocessor::Write", "Multi-write not yet supported.");
        }
        return false;
    }

    bool Write(RawTransponderPacket tpacket, bool require_ack = false) {
        return Write(kAddrRawTransponderPacket, tpacket, require_ack);
    }
    bool Write(SettingsManager::Settings settings_struct, bool require_ack = true) {
        return Write(kAddrSettingsStruct, settings_struct, require_ack);
    }

    /**
     * Top level function that translates a read from an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     * Note that this function is not generally called directly, use the public Write and Read interfaces instead (no
     * address required).
     */
    template <typename T>
    bool Read(SCAddr addr, T &object) {
        if (sizeof(object) < SCResponsePacket::kDataMaxLenBytes) {
            // Single read.
            return PartialRead(addr, (uint8_t *)&object, sizeof(object));

        } else {
            // Multi-read.
            CONSOLE_ERROR("SPICoprocessor::Read", "Multi-read not yet supported.");
        }
        return false;
    }

    // ACKs aren't required for reading since it's already a two way transaction.
    inline bool Read(SettingsManager::Settings settings_struct) { return Read(kAddrSettingsStruct, settings_struct); }

#ifdef ON_PICO

#elif ON_ESP32
#endif

    // /**
    //  * Transmit a packet to the coprocessor. Blocking.
    //  * @param[in] packet Reference to the packet that will be transmitted.
    //  * @retval True if succeeded, false otherwise.
    //  */
    // bool SendMessage(SCMessage &message);

#ifdef ON_PICO
    bool GetSPIHandshakePinLevel() { return gpio_get(config_.spi_handshake_pin); }
#elif ON_ESP32
    /**
     * Helper function used by callbacks to set the handshake pin high or low on the ESP32.
     */
    void SetSPIHandshakePinLevel(bool level) {
        // Only set the handshake pin HI when we know we want to solicit a response and not block + wait.
        // Hanshake pin can always be set low.
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
    void BlinkNetworkLED(uint16_t blink_duration_ms = kNetworkLEDBlinkDurationMs) {
        gpio_set_level(config_.network_led_pin, 1);
        network_led_turn_on_timestamp_ticks_ = xTaskGetTickCount();
        network_led_on = true;
    }

    /**
     * Turns off the network LED if necessary.
     */
    void UpdateNetworkLED() {
        if (network_led_on &&
            xTaskGetTickCount() - network_led_turn_on_timestamp_ticks_ > kNetworkLEDBlinkDurationTicks) {
            gpio_set_level(config_.network_led_pin, 0);
            network_led_on = false;
        }
    }
#endif

   private:
    enum ReturnCode : int { kOk = 0, kErrorGeneric = -1, kErrorTimeout = -2 };

#ifdef ON_ESP32
    SemaphoreHandle_t coprocessor_spi_mutex_;
#endif

    bool PartialWrite(SCAddr addr, uint8_t *object_buf, uint8_t len, uint16_t offset = 0, bool require_ack = false) {
        SCWritePacket write_packet;
#ifdef ON_PICO
        write_packet.cmd = require_ack ? kCmdWriteToSlaveRequireAck : kCmdWriteToSlave;
#elif ON_ESP32
        write_packet.cmd = require_ack ? kCmdWriteToMasterRequireAck : kCmdWriteToMaster;
#endif
        write_packet.addr = addr;
        memcpy(write_packet.data, object_buf + offset, len);
        write_packet.len = len;
        write_packet.offset = offset;
        write_packet.PopulateCRC();

#ifdef ON_ESP32
        use_handshake_pin_ = true;  // Set handshake pin to solicit a transaction with the RP2040.
#endif
        int bytes_written = SPIWriteBlocking(write_packet.GetBuf(), write_packet.GetBufLenBytes(), true);

        if (bytes_written < 0) {
            CONSOLE_ERROR("SPICoprocessor::PartialWrite", "Error code %d while writing object over SPI.",
                          bytes_written);
            return bytes_written;
        }
        if (require_ack && !SPIWaitForAck()) {
            CONSOLE_ERROR("SPICoprocessor::PartialWrite",
                          "Timed out or received bad ack after writing to coprocessor.");
            return false;
        }
        return true;
    }

    bool PartialRead(SCAddr addr, uint8_t *object_buf, uint8_t len, uint16_t offset = 0) {
        SCReadRequestPacket read_request_packet;
#ifdef ON_PICO
        read_request_packet.cmd = kCmdReadFromSlave;
#elif ON_ESP32
        read_request_packet.cmd = kCmdReadFromMaster;
#endif
        read_request_packet.addr = addr;
        read_request_packet.offset = offset;
        read_request_packet.len = len;
        read_request_packet.PopulateCRC();

        uint8_t rx_buf[kSPITransactionMaxLenBytes];

#ifdef ON_ESP32
        use_handshake_pin_ = true;  // Set handshake pin to solicit a transaction with the RP2040.
#endif
        int bytes_exchanged =
            SPIWriteReadBlocking(read_request_packet.GetBuf(), rx_buf, read_request_packet.GetBufLenBytes());
        uint16_t read_request_bytes = read_request_packet.GetBufLenBytes();
        uint8_t *response_buf = rx_buf + read_request_bytes;
        SCResponsePacket response_packet = SCResponsePacket(response_buf, bytes_exchanged - read_request_bytes);
        if (!response_packet.IsValid()) {
            CONSOLE_ERROR("SPICoprocessor::PartialRead",
                          "Received response packet of length %d Bytes with an invalid CRC.",
                          response_packet.GetBufLenBytes());
            return false;
        }
        if (response_packet.cmd != SCCommand::kCmdDataBlock) {
            CONSOLE_ERROR("SPICoprocessor::PartialRead",
                          "Received invalid response with cmd=0x%x to requested read at address 0x%x of length %d with "
                          "offset %d Bytes.",
                          response_packet.cmd, read_request_packet.addr, read_request_packet.len,
                          read_request_packet.offset);
            return false;
        }
        if (response_packet.data_len_bytes != len) {
            CONSOLE_ERROR("SPICoprocessor::PartialRead",
                          "Received incorrect number of Bytes while reading object at address 0x%x with offset %d "
                          "Bytes. Requested %d Bytes but received %d.",
                          addr, offset, read_request_packet.len, response_packet.data_len_bytes);
            return false;
        }
        memcpy(object_buf + offset, response_packet.data, response_packet.data_len_bytes);
        return true;
    }

    /**
     * Setter for writing data to the address space.
     * @param[in] addr Address to write to.
     * @param[in] buf Buffer to read from.
     * @param[in] buf_len Number of Bytes to write.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully wrote, false if address was invalid or something else borked.
     */
    bool SetBytes(SCAddr addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0);

    /**
     * Getter for reading data from the address space.
     @param[in] addr Address to read from.
     @param[out] buf Buffer to write to.
     @param[in] buf_len Number of Bytes to read.
     @param[in] offset Byte offset from beginning of object. Used for partial reads.
     @retval Returns true if successfully read, false if address was invalid or something else borked.
     */
    bool GetBytes(SCAddr addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0);

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
    uint32_t scratch_;  // Scratch register used for testing.

#ifdef ON_PICO
#elif ON_ESP32
    // WORD_ALIGNED_ATTR SPITransaction spi_rx_queue_buf_[kSPITransactionQueueLenTransactions];
    // WORD_ALIGNED_ATTR SPITransaction spi_tx_queue_buf_[kSPITransactionQueueLenTransactions];

    // PFBQueue<SPITransaction> spi_rx_queue_ = PFBQueue<SPITransaction>(
    //     {.buf_len_num_elements = kSPITransactionQueueLenTransactions, .buffer = spi_rx_queue_buf_});
    // PFBQueue<SPITransaction> spi_tx_queue_ = PFBQueue<SPITransaction>(
    //     {.buf_len_num_elements = kSPITransactionQueueLenTransactions, .buffer = spi_tx_queue_buf_});

    bool spi_receive_task_should_exit_ = false;  // Flag used to tell SPI receive task to exit.
    TickType_t network_led_turn_on_timestamp_ticks_ = 0;
    bool network_led_on = false;
    bool use_handshake_pin_ =
        false;  // Allow handshake pin toggle to be skipped if waiting for a mesage and not writing to master.
#endif
};

#ifdef ON_PICO
extern SPICoprocessor esp32;
#elif ON_ESP32
extern SPICoprocessor pico;
#endif

#endif /* SPI_COPROCESSOR_HH_ */