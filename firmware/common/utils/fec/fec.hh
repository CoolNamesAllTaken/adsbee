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
    UATReedSolomon();

    /**
     * Attempt decoding of a short ADS-B message.
     * Buffer will only be modified if decode is successful.
     * @param message_buf Buffer with the encoded message to decode. If decode is successful, buffer will be modified in
     * place to contain the decoded payload. If decode is unsuccessful, buffer will not be modified.
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeShortADSBMessage(uint8_t message_buf[]);

    /**
     * Attempt decoding of a long ADS-B message.
     * Buffer will only be modified if decode is successful.
     * @param message_buf Buffer with the encoded message to decode. If decode is successful, buffer will be modified in
     * place to contain the decoded payload. If decode is unsuccessful, buffer will not be modified
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeLongADSBMessage(uint8_t message_buf[]);

    /**
     * Attempt decoding of a UAT uplink message.
     * @param[out] decoded_payload_buf Buffer to store the decoded payload in. If decode is successful, buffer will be
     * modified. This buffer needs to be oversized by the number of FEC parity bytes in a UAT uplink message block since
     * blocks are processed in-place, and the last block needs a place to overflow to.
     * @param[in] encoded_message_buf Buffer with the encoded message to decode.
     * @return Number of bits corrected. 0 if message had no errors, positive number if errors were corrected, -1 if
     * message was invalid and not correctable.
     */
    int DecodeUplinkMessage(uint8_t decoded_payload_buf[], uint8_t encoded_message_buf[]);

    /**
     * Test functions used to turning test messages (provided without FEC headers) into encoded messages similar to what
     * would be found on the air.
     */
    bool EncodeShortADSBMessage(uint8_t message_buf[]);
    bool EncodeLongADSBMessage(uint8_t message_buf[]);
    bool EncodeUplinkMessage(uint8_t encoded_message_buf[], uint8_t decoded_payload_buf[]);

    void* rs_adsb_short = nullptr;
    void* rs_adsb_long = nullptr;
    void* rs_uplink = nullptr;
};

/**
 * WARNING: The Reed-Solomon decoder below needs to be initialized by an external function before it can be used.
 */
extern UATReedSolomon uat_rs;