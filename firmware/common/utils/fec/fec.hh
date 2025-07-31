#pragma once
extern "C" {
#include "rs.h"
}
#include "unit_conversions.hh"  // For CeilBitsToBytes

/**
 * This file contains wrappers for the FEC encode / decode functions that make them convenient to use when decoding UAT
 * messages. Constants for message block lengths and Reed-Solomon parameters are defined here.
 */

class UATReedSolomon {
   public:
    /**
     * UAT downlink message parameters.
     */
    static const uint16_t kShortADSBMessagePayloadNumBits = 144;
    static const uint16_t kShortADSBMessagePayloadNumBytes = CeilBitsToBytes(kShortADSBMessagePayloadNumBits);
    static const uint16_t kShortADSBMessageFECParityNumBits = 96;
    static const uint16_t kShortADSBMessageFECParityNumBytes = CeilBitsToBytes(kShortADSBMessageFECParityNumBits);
    static const uint16_t kShortADSBMessageNumBits =
        kShortADSBMessagePayloadNumBits + kShortADSBMessageFECParityNumBits;
    static const uint16_t kShortADSBMessageNumBytes = CeilBitsToBytes(kShortADSBMessageNumBits);

    static const uint16_t kLongADSBMessagePayloadNumBits = 272;
    static const uint16_t kLongADSBMessagePayloadNumBytes = CeilBitsToBytes(kLongADSBMessagePayloadNumBits);
    static const uint16_t kLongADSBMessageFECParityNumBits = 112;
    static const uint16_t kLongADSBMessageFECParityNumBytes = CeilBitsToBytes(kLongADSBMessageFECParityNumBits);
    static const uint16_t kLongADSBMessageNumBits = kLongADSBMessagePayloadNumBits + kLongADSBMessageFECParityNumBits;
    static const uint16_t kLongADSBMessageNumBytes = CeilBitsToBytes(kLongADSBMessageNumBits);

    static const uint16_t kADSBMessageMaxSizeBytes =
        kLongADSBMessagePayloadNumBytes + kLongADSBMessageFECParityNumBytes;  // For convenience.

    /**
     * UAT uplink message parameters.
     */
    static const uint16_t kUplinkMessageNumBlocks = 6;
    static const uint16_t kUplinkMessageBlockPayloadNumBytes = 72;
    static const uint16_t kUplinkMessageBlockFECParityNumBytes = 20;
    static const uint16_t kUplinkMessageBlockNumBytes =
        kUplinkMessageBlockPayloadNumBytes + kUplinkMessageBlockFECParityNumBytes;

    static const uint16_t kUplinkMessagePayloadNumBytes = kUplinkMessageNumBlocks * kUplinkMessageBlockPayloadNumBytes;

    static const uint16_t kUplinkMessageMaxSizeBytes =
        kUplinkMessageNumBlocks * kUplinkMessageBlockNumBytes;  // Maximum size of a UAT uplink message.

    UATReedSolomon();

    /**
     * Attempt decoding of a short ADS-B message.
     * Buffer will only be modified if decode is successful.
     * @param message_buf Buffer with the encoded message to decode. If decode is successful, buffer will be modified in
     * place to contain the decoded payload. If decode is unsuccessful, buffer will not be modified.
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeShortADSBMessage(uint8_t message_buf[kShortADSBMessageNumBytes]);

    /**
     * Attempt decoding of a long ADS-B message.
     * Buffer will only be modified if decode is successful.
     * @param message_buf Buffer with the encoded message to decode. If decode is successful, buffer will be modified in
     * place to contain the decoded payload. If decode is unsuccessful, buffer will not be modified
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeLongADSBMessage(uint8_t message_buf[kLongADSBMessageNumBytes]);

    /**
     * Attempt decoding of a UAT uplink message.
     * @param encoded_message_buf Buffer with the encoded message to decode.
     * @param decoded_payload_buf Buffer to store the decoded payload in. If decode is successful, buffer will be
     * modified. This buffer needs to be oversized by the number of FEC parity bytes in a UAT uplink message block since
     * blocks are processed in-place, and the last block needs a place to overflow to.
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeUplinkMessage(
        uint8_t encoded_message_buf[kUplinkMessageMaxSizeBytes],
        uint8_t decoded_payload_buf[kUplinkMessagePayloadNumBytes + kUplinkMessageBlockFECParityNumBytes]);

    void* rs_adsb_short = nullptr;
    void* rs_adsb_long = nullptr;
    void* rs_uplink = nullptr;
};

/**
 * WARNING: The Reed-Solomon decoder below needs to be initialized by an external function before it can be used.
 */
extern UATReedSolomon uat_rs;