#include "comms.hh"
#include "settings.hh"

bool CommsManager::ReportRaw(
#ifdef ON_ESP32
    uint16_t iface,  // iface = feed index
#else
    SettingsManager::SerialInterface iface,  // iface = serial interface
#endif
    const CompositeArray::RawPackets &packets) {
    char error_msg[CompositeArray::RawPackets::kErrorMessageMaxLen];
    if (!packets.IsValid(error_msg)) {
        CONSOLE_ERROR("CommsManager::ReportRaw", "Invalid CompositeArray::RawPackets: %s", error_msg);
        return false;
    }

    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        char raw_frame_buf[kRawModeSFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawModeSFrame(packets.mode_s_packets[i], raw_frame_buf);
        SendBuf(iface, (char *)raw_frame_buf, num_bytes_in_frame);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        char raw_frame_buf[kRawUATADSBFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATADSBFrame(packets.uat_adsb_packets[i], raw_frame_buf);
        SendBuf(iface, (char *)raw_frame_buf, num_bytes_in_frame);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        char raw_frame_buf[kRawUATUplinkFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATUplinkFrame(packets.uat_uplink_packets[i], raw_frame_buf);
        SendBuf(iface, (char *)raw_frame_buf, num_bytes_in_frame);
    }
    return true;
}

bool CommsManager::ReportBeast(
#ifdef ON_ESP32
    uint16_t iface,  // iface = feed index
#else
    SettingsManager::SerialInterface iface,  // iface = serial interface
#endif
    const CompositeArray::RawPackets &packets) {
    char error_msg[CompositeArray::RawPackets::kErrorMessageMaxLen];
    if (!packets.IsValid(error_msg)) {
        CONSOLE_ERROR("CommsManager::ReportBeast", "Invalid CompositeArray::RawPackets: %s", error_msg);
        return false;
    }

    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kModeSBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame = BeastReporter::BuildModeSBeastFrame(beast_frame_buf, packets.mode_s_packets[i]);
        SendBuf(iface, (char *)beast_frame_buf, num_bytes_in_frame);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kUATADSBBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame =
            BeastReporter::BuildUATADSBBeastFrame(beast_frame_buf, packets.uat_adsb_packets[i]);
        SendBuf(iface, (char *)beast_frame_buf, num_bytes_in_frame);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kUATUplinkBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame =
            BeastReporter::BuildUATUplinkBeastFrame(beast_frame_buf, packets.uat_uplink_packets[i]);
        SendBuf(iface, (char *)beast_frame_buf, num_bytes_in_frame);
    }
    return true;
}