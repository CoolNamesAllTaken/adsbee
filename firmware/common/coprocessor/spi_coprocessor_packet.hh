#pragma once

#include "buffer_utils.hh"
#include "object_dictionary.hh"
#include "stdint.h"

class SPICoprocessorPacket {
   public:
    static constexpr uint16_t kSPITransactionMaxLenBytes =
        4096;  // Default max is 4096 Bytes on ESP32 (with DMA) and 4096 Bytes on RP2040.
    static_assert(kSPITransactionMaxLenBytes % 4 == 0);  // Make sure it's word-aligned.

    /** NOTE: Packets should not be used outside of the SPICoprocessorInterface class and its children, they are only
     * exposed for testing. **/
    /**
     * Abstract base struct for SPI Coprocessor packets.
     */
    struct __attribute__((__packed__)) SCPacket {
        static constexpr uint16_t kPacketMaxLenBytes = kSPITransactionMaxLenBytes;
        static constexpr uint16_t kCRCLenBytes = sizeof(uint16_t);

        using SCCommand = ObjectDictionary::SCCommand;  // Use the SCCommand enum from ObjectDictionary.

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
        SCCommand cmd = SCCommand::kCmdInvalid;
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
        SCCommand cmd = SCCommand::kCmdInvalid;
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
        // ADDR = SCCommand::kCmdAck
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
        SCCommand cmd = SCCommand::kCmdInvalid;
        uint8_t data[kDataMaxLenBytes + kCRCLenBytes];
        /** End packet contents on the wire. **/

        uint16_t data_len_bytes = 0;  // Length from start of data to beginning of CRC.

        /**
         * Default constructor.
         */
        SCResponsePacket() {
            // memset(data, 0x0, kDataMaxLenBytes);
        }

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