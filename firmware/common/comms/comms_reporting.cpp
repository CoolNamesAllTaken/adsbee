#include "comms.hh"
#include "hal.hh"  // For timestamping.
#include "settings.hh"

// Reporting utils.
#include "beast_utils.hh"
#include "csbee_utils.hh"
#include "gdl90_utils.hh"
#include "mavlink_utils.hh"
#include "raw_utils.hh"

#ifdef ON_ESP32
AircraftDictionary &aircraft_dictionary = adsbee_server.aircraft_dictionary;
#else
#include "adsbee.hh"  // For access to the aircraft dictionary.
AircraftDictionary &aircraft_dictionary = adsbee.aircraft_dictionary;
#endif

GDL90Reporter gdl90;

bool CommsManager::UpdateReporting(const ReportSink *sinks, const SettingsManager::ReportingProtocol *sink_protocols,
                                   uint16_t num_sinks, const CompositeArray::RawPackets *packets_to_report) {
    bool ret = true;
    uint32_t timestamp_ms = get_time_since_boot_ms();

    // Build lists of sinks for each reporting protocol.
    ReportSink raw_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink beast_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink csbee_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink mavlink1_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink mavlink2_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink gdl90_sinks[SettingsManager::kNumSerialInterfaces];

    uint16_t num_raw_sinks = 0, num_beast_sinks = 0, num_csbee_sinks = 0, num_mavlink1_sinks = 0,
             num_mavlink2_sinks = 0, num_gdl90_sinks = 0;

    for (uint16_t i = 0; i < num_sinks; i++) {
        switch (sink_protocols[i]) {
            case SettingsManager::kNoReports:
                break;  // Not a reporting protocol.
            case SettingsManager::kRaw:
                raw_sinks[num_raw_sinks++] = sinks[i];
                break;
            case SettingsManager::kBeast:
                beast_sinks[num_beast_sinks++] = sinks[i];
                break;
            case SettingsManager::kCSBee:
                csbee_sinks[num_csbee_sinks++] = sinks[i];
                break;
            case SettingsManager::kMAVLINK1:
                mavlink1_sinks[num_mavlink1_sinks++] = sinks[i];
                break;
            case SettingsManager::kMAVLINK2:
                mavlink2_sinks[num_mavlink2_sinks++] = sinks[i];
                break;
            case SettingsManager::kGDL90:
                gdl90_sinks[num_gdl90_sinks++] = sinks[i];
                break;
            default:
                CONSOLE_ERROR("CommsManager::UpdateReporting",
                              "Unrecognized reporting protocol %s on interface %s, skipping.",
                              SettingsManager::kSerialInterfaceStrs[sinks[i]],
                              SettingsManager::kReportingProtocolStrs[sink_protocols[i]]);
                break;  // Not a periodic report protocol.
        }
    }

    /**  Report Raw Packets **/
    if (packets_to_report->len_bytes > sizeof(CompositeArray::RawPackets::Header)) {
        // Only report raw packets if they are provided (still send locally decoded reports even if no raw packets).
        if (!ReportRaw(raw_sinks, num_raw_sinks, *packets_to_report)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportRaw.");
            ret = false;
        }
        if (!ReportBeast(beast_sinks, num_beast_sinks, *packets_to_report)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportBeast.");
            ret = false;
        }
    }

    /** Locally Decoded Reports **/
    if (num_csbee_sinks > 0 && timestamp_ms - last_csbee_report_timestamp_ms_ >= kCSBeeReportingIntervalMs) {
        if (!ReportCSBee(csbee_sinks, num_csbee_sinks)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportCSBee.");
            ret = false;
        }
        last_csbee_report_timestamp_ms_ = timestamp_ms;
    }
    if (timestamp_ms - last_mavlink_report_timestamp_ms_ >= kMAVLINKReportingIntervalMs) {
        if (num_mavlink1_sinks > 0 && !ReportMAVLINK(mavlink1_sinks, num_mavlink1_sinks, 1)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportMAVLINK with MAVLINK1 sinks.");
            ret = false;
        }
        if (num_mavlink2_sinks > 0 && !ReportMAVLINK(mavlink2_sinks, num_mavlink2_sinks, 2)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportMAVLINK with MAVLINK2 sinks.");
            ret = false;
        }
        last_mavlink_report_timestamp_ms_ = timestamp_ms;
    }
    if (num_gdl90_sinks > 0 && timestamp_ms - last_gdl90_report_timestamp_ms_ >= kGDL90ReportingIntervalMs) {
        if (!ReportGDL90(gdl90_sinks, num_gdl90_sinks)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportGDL90.");
            ret = false;
        }
        last_gdl90_report_timestamp_ms_ = timestamp_ms;
    }

    return ret;
}

bool CommsManager::ReportRaw(ReportSink *sinks, uint16_t num_sinks, const CompositeArray::RawPackets &packets) {
    char error_msg[CompositeArray::RawPackets::kErrorMessageMaxLen] = {0};
    if (!packets.IsValid(error_msg)) {
        CONSOLE_ERROR("CommsManager::ReportRaw", "Invalid CompositeArray::RawPackets: %s", error_msg);
        return false;
    }

    bool ret = true;
    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        char raw_frame_buf[kRawModeSFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawModeSFrame(packets.mode_s_packets[i], raw_frame_buf);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)raw_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        char raw_frame_buf[kRawUATADSBFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATADSBFrame(packets.uat_adsb_packets[i], raw_frame_buf);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)raw_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        char raw_frame_buf[kRawUATUplinkFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATUplinkFrame(packets.uat_uplink_packets[i], raw_frame_buf);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)raw_frame_buf, num_bytes_in_frame);
        }
    }
    return ret;
}

bool CommsManager::ReportBeast(ReportSink *sinks, uint16_t num_sinks, const CompositeArray::RawPackets &packets) {
    char error_msg[CompositeArray::RawPackets::kErrorMessageMaxLen] = {0};
    if (!packets.IsValid(error_msg)) {
        CONSOLE_ERROR("CommsManager::ReportBeast", "Invalid CompositeArray::RawPackets: %s", error_msg);
        return false;
    }

    bool ret = true;
    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kModeSBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame = BeastReporter::BuildModeSBeastFrame(beast_frame_buf, packets.mode_s_packets[i]);

        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)beast_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kUATADSBBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame =
            BeastReporter::BuildUATADSBBeastFrame(beast_frame_buf, packets.uat_adsb_packets[i]);

        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)beast_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        uint8_t beast_frame_buf[BeastReporter::kUATUplinkBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame =
            BeastReporter::BuildUATUplinkBeastFrame(beast_frame_buf, packets.uat_uplink_packets[i]);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char *)beast_frame_buf, num_bytes_in_frame);
        }
    }
    return ret;
}

bool CommsManager::ReportCSBee(ReportSink *sinks, uint16_t num_sinks) {
    bool ret = true;

    // Write out a CSBee Aircraft message for each aircraft in the aircraft dictionary.
    for (auto &itr : aircraft_dictionary.dict) {
        char message[kCSBeeMessageStrMaxLen];
        int message_len_bytes = -1;

        if (ModeSAircraft *mode_s_aircraft = get_if<ModeSAircraft>(&(itr.second)); mode_s_aircraft) {
            message_len_bytes = WriteCSBeeModeSAircraftMessageStr(message, *mode_s_aircraft);
        } else if (UATAircraft *uat_aircraft = get_if<UATAircraft>(&(itr.second)); uat_aircraft) {
            message_len_bytes = WriteCSBeeUATAircraftMessageStr(message, *uat_aircraft);
        } else {
            CONSOLE_WARNING("CommsManager::ReportCSBee", "Unknown aircraft type in dictionary for UID 0x%lx.",
                            itr.first);
            continue;
        }

        if (message_len_bytes < 0) {
            CONSOLE_ERROR("CommsManager::ReportCSBee",
                          "Encountered an error in WriteCSBeeAircraftMessageStr, error code %d.", message_len_bytes);
            return false;
        }
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], message, message_len_bytes);
        }
    }

    // Write a CSBee Statistics message.
    char message[kCSBeeMessageStrMaxLen];
    int16_t message_len_bytes =
        WriteCSBeeStatisticsMessageStr(message,                                            // Buffer to write into.
                                       aircraft_dictionary.metrics.demods_1090,            // DPS
                                       aircraft_dictionary.metrics.raw_squitter_frames,    // RAW_SFPS
                                       aircraft_dictionary.metrics.valid_squitter_frames,  // SFPS
                                       aircraft_dictionary.metrics.raw_extended_squitter_frames,    // RAW_ESFPS
                                       aircraft_dictionary.metrics.valid_extended_squitter_frames,  // ESFPS
                                       aircraft_dictionary.metrics.raw_uat_adsb_frames,             // RAW_UAT
                                       aircraft_dictionary.metrics.valid_uat_adsb_frames,           // VALID_UAT
                                       aircraft_dictionary.GetNumAircraft(),                        // NUM_AIRCRAFT
                                       0u,                                                          // TSCAL
                                       get_time_since_boot_ms() / 1000                              // UPTIME
        );
    if (message_len_bytes < 0) {
        CONSOLE_ERROR("CommsManager::ReportCSBee",
                      "Encountered an error in WriteCSBeeStatisticsMessageStr, error code %d.", message_len_bytes);
        return false;
    }

    for (uint16_t i = 0; i < num_sinks; i++) {
        ret &= SendBuf(sinks[i], message, message_len_bytes);
    }
    return ret;
}

bool CommsManager::ReportMAVLINK(ReportSink *sinks, uint16_t num_sinks, uint8_t mavlink_version) {
    if (num_sinks == 0) {
        CONSOLE_WARNING("CommsManager::ReportMAVLINK", "No MAVLINK sinks provided.");
        return false;
    }
    if (mavlink_version != 1 && mavlink_version != 2) {
        CONSOLE_ERROR("CommsManager::ReportMAVLINK", "MAVLINK version %d does not exist.", mavlink_version);
        return false;
    }
    mavlink_set_proto_version(SettingsManager::SerialInterface::kCommsUART, mavlink_version);

    // Send a HEARTBEAT message.
    mavlink_heartbeat_t heartbeat_msg = {.custom_mode = 0,
                                         .type = MAV_TYPE_ADSB,
                                         .autopilot = MAV_AUTOPILOT_INVALID,
                                         .base_mode = 0,
                                         .system_status = MAV_STATE_ACTIVE,
                                         .mavlink_version = mavlink_version};
    for (uint16_t i = 0; i < num_sinks; i++) {
        mavlink_msg_heartbeat_send_struct(static_cast<mavlink_channel_t>(sinks[i]), &heartbeat_msg);
    }

    // Send an ADSB_VEHICLE message for each aircraft in the dictionary.
    for (auto &itr : aircraft_dictionary.dict) {
        mavlink_adsb_vehicle_t adsb_vehicle_msg;
        if (ModeSAircraft *mode_s_aircraft = get_if<ModeSAircraft>(&(itr.second)); mode_s_aircraft) {
            adsb_vehicle_msg = ModeSAircraftToMAVLINKADSBVehicleMessage(*mode_s_aircraft);
        } else if (UATAircraft *uat_aircraft = get_if<UATAircraft>(&(itr.second)); uat_aircraft) {
            adsb_vehicle_msg = UATAircraftToMAVLINKADSBVehicleMessage(*uat_aircraft);
        } else {
            CONSOLE_WARNING("CommsManager::ReportMAVLINK", "Unknown aircraft type in dictionary for UID 0x%lx.",
                            itr.first);
            continue;
        }
        // Send the message.
        for (uint16_t i = 0; i < num_sinks; i++) {
            mavlink_msg_adsb_vehicle_send_struct(static_cast<mavlink_channel_t>(sinks[i]), &adsb_vehicle_msg);
        }
    }
    // Send delimiter message.
    switch (mavlink_version) {
        case 1: {
            mavlink_request_data_stream_t request_data_stream_msg = {0};
            for (uint16_t i = 0; i < num_sinks; i++) {
                mavlink_msg_request_data_stream_send_struct(static_cast<mavlink_channel_t>(sinks[i]),
                                                            &request_data_stream_msg);
            }
            break;
        }
        case 2: {
            mavlink_message_interval_t message_interval_msg = {
                .interval_us = (int32_t)(kMAVLINKReportingIntervalMs * (uint32_t)kUsPerMs),
                .message_id = MAVLINK_MSG_ID_ADSB_VEHICLE};
            for (uint16_t i = 0; i < num_sinks; i++) {
                mavlink_msg_message_interval_send_struct(static_cast<mavlink_channel_t>(sinks[i]),
                                                         &message_interval_msg);
            }
            break;
        }
        default:
            CONSOLE_ERROR("CommsManager::ReportMAVLINK", "MAVLINK version %d does not exist.", mavlink_version);
            return false;
    };

    return true;
}

bool CommsManager::ReportGDL90(ReportSink *sinks, uint16_t num_sinks) {
    bool ret = true;

    uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
    uint16_t msg_len;

    // Heartbeat Message
    msg_len = gdl90.WriteGDL90HeartbeatMessage(buf, get_time_since_boot_ms() / 1000,
                                               aircraft_dictionary.metrics.valid_extended_squitter_frames);

    for (uint16_t i = 0; i < num_sinks; i++) {
        ret &= SendBuf(sinks[i], (char *)buf, msg_len);
    }

    // Ownship Report
    GDL90Reporter::GDL90TargetReportData ownship_data;
    // TODO: Actually fill out ownship data!
    msg_len = gdl90.WriteGDL90TargetReportMessage(buf, ownship_data, true);
    for (uint16_t i = 0; i < num_sinks; i++) {
        ret &= SendBuf(sinks[i], (char *)buf, msg_len);
    }

    // Traffic Reports
    for (auto &itr : aircraft_dictionary.dict) {
        msg_len = 0;
        if (ModeSAircraft *mode_s_aircraft = get_if<ModeSAircraft>(&(itr.second)); mode_s_aircraft) {
            msg_len = gdl90.WriteGDL90TargetReportMessage(buf, *mode_s_aircraft, false);
        } else if (UATAircraft *uat_aircraft = get_if<UATAircraft>(&(itr.second)); uat_aircraft) {
            msg_len = gdl90.WriteGDL90TargetReportMessage(buf, *uat_aircraft, false);
        } else {
            CONSOLE_WARNING("CommsManager::ReportGDL90", "Unknown aircraft type in dictionary for UID 0x%lx.",
                            itr.first);
            continue;
        }
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], (char *)buf, msg_len);
        }
    }
    return ret;
}