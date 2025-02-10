#pragma once
#include "stdint.h"

class NASACPRDecoder {
   public:
    struct DecodedPosition {
        float lat_deg;
        float lon_deg;
    };

    struct CPRMessage {
        bool odd;
        uint32_t lat_cpr;
        uint32_t lon_cpr;
    };

    /**
     * Decodes a CPR location for an airborne position using an existing reference position.
     * @param[in] reference_position The reference position to use for decoding. The "valid" property is ignored.
     * @param[in] message The CPR message to decode.
     * @param[out] decoded_position The decoded location.
     * @return True if the decode succeeded (recovered_position is valid), false otherwise.
     */
    static bool DecodeAirborneLocalCPR(const DecodedPosition &reference_position, const CPRMessage &message,
                                       DecodedPosition &decoded_position);

    /**
     * Decodes a CPR location for an airborne position using two CPR messages. Note that message1 is considered the more
     * recent message.
     * @param[in] message0 The first CPR message.
     * @param[in] message1 The second CPR message.
     * @param[out] decoded_position The decoded location.
     * @return True if the decode succeeded (recovered_position is valid), false otherwise.
     */
    static bool DecodeAirborneGlobalCPR(const CPRMessage &message0, const CPRMessage &message1,
                                        DecodedPosition &decoded_position);
};
