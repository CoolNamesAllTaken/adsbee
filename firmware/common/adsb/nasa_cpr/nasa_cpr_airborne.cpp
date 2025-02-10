#include "airborne/cpr.h"
#include "awb_utils.h"
#include "nasa_cpr.hh"

bool NASACPRDecoder::DecodeAirborneLocalCPR(const DecodedPosition &reference_position, const CPRMessage &message,
                                            DecodedPosition &decoded_position) {
    // For some reason local_dec doesn't use the struct message format field, so we need to manually tell it whether the
    // incoming packet is odd or even.
    struct recovered_position result =
        local_dec(message.odd, lat2awb(reference_position.lat_deg), lon2awb(reference_position.lon_deg),
                  {.format = message.odd, .yz = message.lat_cpr, .xz = message.lon_cpr});
    decoded_position.lat_deg = awb2lat(result.lat_awb);
    decoded_position.lon_deg = awb2lon(result.lon_awb);
    return result.valid;
};

bool NASACPRDecoder::DecodeAirborneGlobalCPR(const CPRMessage &message0, const CPRMessage &message1,
                                             DecodedPosition &decoded_position) {
    struct recovered_position result =
        global_dec(message1.odd, {.format = message0.odd, .yz = message0.lat_cpr, .xz = message0.lon_cpr},
                   {.format = message1.odd, .yz = message1.lat_cpr, .xz = message1.lon_cpr});
    decoded_position.lat_deg = awb2lat(result.lat_awb);
    decoded_position.lon_deg = awb2lon(result.lon_awb);
    return result.valid;
}