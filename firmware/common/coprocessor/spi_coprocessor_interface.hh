#pragma once

#ifdef ON_PICO
#include <functional>  // For std::function.

#include "bsp.hh"
#include "hardware/gpio.h"
#include "hardware/spi.h"
#elif defined(ON_ESP32)
#include "bsp.hh"
#include "data_structures.hh"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#endif

#ifdef ON_PICO
#define ON_COPRO_MASTER
#elif defined(ON_ESP32) || defined(ON_TI)
#define ON_COPRO_SLAVE
#endif

class SPICoprocessorInterface {
   public:
    static constexpr uint16_t kSPITransactionMaxLenBytes =
        4096;  // Default max is 4096 Bytes on ESP32 (with DMA) and 4096 Bytes on RP2040.
    static_assert(kSPITransactionMaxLenBytes % 4 == 0);  // Make sure it's word-aligned.

    static constexpr uint16_t kErrorMessageMaxLen = 500;
    enum ReturnCode : int {
        kOk = 0,  // All good.
        kErrorGeneric = -1,
        kErrorTimeout = -2,
        kErrorHandshakeHigh = -3  // Used on the Master to indicate that a transaction was aborted because the slave was
                                  // tryingto talk at the same time as the master.
    };

    /**
     * Convert a ReturnCode to a human-readable string.
     * @param[in] code The ReturnCode to convert.
     * @retval String representation of the ReturnCode.
     */
    static const char *ReturnCodeToString(ReturnCode code) {
        switch (code) {
            case kOk:
                return "OK";
            case kErrorGeneric:
                return "Generic Error";
            case kErrorTimeout:
                return "Timeout Error";
            case kErrorHandshakeHigh:
                return "Handshake High Error";
            default:
                return "Unknown Error";
        }
    }

    /** NOTE: Packets should not be used outside of the SPICoprocessorInterface class and its children, they are only
     * exposed for testing. **/

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
};

/**
 * Abstract interface for interacting with a SPI coprocessor master. For instance, this is used to interact with the
 * RP2040 (coprocessor master) on the ESP32 (coprocessor slave).
 */
class SPICoprocessorMasterInterface : public SPICoprocessorInterface {
   public:
    /**
     * Initialize the SPI coprocessor master interface.
     * @retval True if initialization was successful, false otherwise.
     */
    virtual bool Init() = 0;

    /**
     * Deinitialize the SPI coprocessor master interface.
     * @retval True if deinitialization was successful, false otherwise.
     */
    virtual bool DeInit() = 0;

    /**
     * Determine whether the handshake pin will be used during the next SPI transaction to solicit a response.
     * @param[in] level True to set pin high once SPI peripheral is loaded up, false to set pin low.
     */
    virtual inline void SPIUseHandshakePin(bool level) = 0;

    virtual inline bool SPIBeginTransaction() = 0;
    virtual inline void SPIEndTransaction() = 0;
    virtual inline bool SPIClaimNextTransaction() = 0;
    virtual inline void SPIReleaseNextTransaction() = 0;
    virtual int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                                     bool end_transaction = true) = 0;

    virtual inline void UpdateNetworkLED() = 0;
};

class SPICoprocessorSlaveInterface : public SPICoprocessorInterface {
   public:
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
    static constexpr uint32_t kSPITransactionTimeoutMs = 20;
    // How long a blocking wait for a handshake can last.
    static constexpr uint32_t kSPIHandshakeTimeoutMs = 20;
    // How long to loop in Update() for after initializing the device in order to allow it to query for settings data.
    static constexpr uint32_t kBootupDelayMs = 500;

    /**
     * Initialize the SPI coprocessor slave interface.
     * @retval True if initialization was successful, false otherwise.
     */
    virtual bool Init() = 0;

    /**
     * Deinitialize the SPI coprocessor slave interface.
     * @retval True if deinitialization was successful, false otherwise.
     */
    virtual bool DeInit() = 0;

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
    virtual bool SPIGetHandshakePinLevel(bool blocking = true) = 0;

    /**
     * Blocks on waiting for the handshake pin to go high, until a timeout is reached.
     * @retval True if handshake line went high before timeout, false otherwise.
     */
    inline bool SPIWaitForHandshake() {
        uint32_t wait_begin_timestamp_ms = get_time_since_boot_ms();
        expecting_handshake_ = true;  // Set this so that we know we are expecting the handshake line to go high.
        while (true) {
            if (SPIGetHandshakePinLevel(false)) {
                // Received handshake signal during non-blocking check.
                break;
            }
            if (get_time_since_boot_ms() - wait_begin_timestamp_ms >= kSPIHandshakeTimeoutMs) {
                // Timed out.
                expecting_handshake_ = false;  // Reset this so that we don't think we are expecting a handshake.
                return false;
            }
        }
        return true;
    }

    virtual bool IsEnabled() = 0;
    virtual void SetEnable(bool enabled) = 0;

    virtual bool SPIBeginTransaction() = 0;
    virtual void SPIEndTransaction() = 0;
    virtual inline bool SPIClaimNextTransaction() = 0;
    virtual inline void SPIReleaseNextTransaction() = 0;
    virtual int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                                     bool end_transaction = true) = 0;

   protected:
    // Use this flag to indicate whether we are expecting the handshake line to go high. If it is high during a
    // transaction when we aren't expecting it, that means that we are stomping on the slave! Not good.
    bool expecting_handshake_ = false;
};