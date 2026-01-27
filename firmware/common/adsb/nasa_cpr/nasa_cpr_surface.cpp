#include "awb_utils.h"
#include "comms.hh"
#include "nasa_cpr.hh"
#include "surface/cpr.hh"

bool NASACPRDecoder::DecodeSurfaceLocalCPR(const DecodedPosition& reference_position, const CPRMessage& message,
                                           DecodedPosition& decoded_position) {
    // For some reason local_dec doesn't use the struct message format field, so we need to manually tell it whether the
    // incoming packet is odd or even.
    nasa_cpr::surface::recovered_position result = nasa_cpr::surface::local_dec(
        message.odd, lat2awb(reference_position.lat_deg), lon2awb(reference_position.lon_deg),
        {.format = message.odd, .yz = message.lat_cpr, .xz = message.lon_cpr});
    decoded_position.lat_deg = awb2lat(result.lat_awb);
    decoded_position.lon_deg = awb2lon(result.lon_awb);
    return result.valid;
};

bool NASACPRDecoder::DecodeSurfaceGlobalCPR(const CPRMessage& even_message, const CPRMessage& odd_message,
                                            uint32_t own_lat_awb, DecodedPosition& decoded_position) {
    if (even_message.odd == odd_message.odd) {
        CONSOLE_ERROR("NASACPRDecoder::DecodeSurfaceGlobalCPR", "Can't perform CPR decode with two %s messages.",
                      even_message.odd ? "odd" : "even");
        return false;  // Both messages must be one odd and one even.
    }

    nasa_cpr::surface::recovered_position result = nasa_cpr::surface::global_dec(
        odd_message.received_timestamp_ms > even_message.received_timestamp_ms,
        {.format = even_message.odd, .yz = even_message.lat_cpr, .xz = even_message.lon_cpr},
        {.format = odd_message.odd, .yz = odd_message.lat_cpr, .xz = odd_message.lon_cpr}, own_lat_awb);
    decoded_position.lat_deg = awb2lat(result.lat_awb);
    decoded_position.lon_deg = awb2lon(result.lon_awb);
    decoded_position.lat_awb = result.lat_awb;
    decoded_position.lon_awb = result.lon_awb;
    if (!result.valid) {
        CONSOLE_WARNING("NASACPRDecoder::DecodeSurfaceGlobalCPR",
                        "Can't decode CPR packets from different latitude zones.");
    }
    return result.valid;  // False if aircraft crossed between latitude zones between messages.
}