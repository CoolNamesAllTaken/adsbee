#include "comms.hh"
#include "hal.hh"  // For timestamping.
#include "settings.hh"

// Reporting utils.
#include "beast_utils.hh"
#include "csbee_utils.hh"
#include "gdl90_utils.hh"
#include "mavlink_utils.hh"
#include "raw_utils.hh"
#include "uat_packet.hh"  // For DecodedUATUplinkPacket.

#ifdef ON_ESP32
AircraftDictionary& aircraft_dictionary = adsbee_server.aircraft_dictionary;
#else
#include "adsbee.hh"  // For access to the aircraft dictionary.
AircraftDictionary& aircraft_dictionary = adsbee.aircraft_dictionary;
#endif

GDL90Reporter gdl90;

bool CommsManager::UpdateReporting(const ReportSink* sinks, const SettingsManager::ReportingProtocol* sink_protocols,
                                   uint16_t num_sinks, const CompositeArray::RawPackets* packets_to_report) {
    bool ret = true;
    uint32_t timestamp_ms = get_time_since_boot_ms();

    // Build lists of sinks for each reporting protocol.
    ReportSink raw_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink beast_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink beast_no_uat_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink beast_no_uat_uplink_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink csbee_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink mavlink1_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink mavlink2_sinks[SettingsManager::kNumSerialInterfaces];
    ReportSink gdl90_sinks[SettingsManager::kNumSerialInterfaces];

    uint16_t num_raw_sinks = 0, num_beast_sinks = 0, num_beast_no_uat_sinks = 0, num_beast_no_uat_uplink_sinks = 0,
             num_csbee_sinks = 0, num_mavlink1_sinks = 0, num_mavlink2_sinks = 0, num_gdl90_sinks = 0;

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
            case SettingsManager::kBeastNoUAT:
                beast_no_uat_sinks[num_beast_no_uat_sinks++] = sinks[i];
                break;
            case SettingsManager::kBeastNoUATUplink:
                beast_no_uat_uplink_sinks[num_beast_no_uat_uplink_sinks++] = sinks[i];
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
        // Send all inclusive Beast reports.
        if (!ReportBeast(beast_sinks, num_beast_sinks, *packets_to_report)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportBeast.");
            ret = false;
        }
        // Send No UAT Beast reports.
        if (!ReportBeast(beast_no_uat_sinks, num_beast_no_uat_sinks, *packets_to_report,
                         SettingsManager::kBeastNoUAT)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportBeast with no UAT.");
            ret = false;
        }
        // Send No UAT Uplink Beast reports.
        if (!ReportBeast(beast_no_uat_uplink_sinks, num_beast_no_uat_uplink_sinks, *packets_to_report,
                         SettingsManager::kBeastNoUATUplink)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportBeast with no UAT or Uplink.");
            ret = false;
        }
        // Send GDL90 reports (UAT uplink only).
        if (!ReportGDL90Uplink(gdl90_sinks, num_gdl90_sinks, *packets_to_report)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during GDL90 UAT uplink report.");
            ret = false;
        }
    }

    /** Locally Decoded Reports **/
    // All locally-decoded protocols share a UID snapshot and a single 1000ms reporting interval.
    // A new round starts only when every active protocol has finished its previous round.

    // If a protocol lost its sinks mid-round, deactivate it so it doesn't block other protocols.
    if (csbee_round_active_ && num_csbee_sinks == 0) csbee_round_active_ = false;
    if (mavlink1_round_active_ && num_mavlink1_sinks == 0) mavlink1_round_active_ = false;
    if (mavlink2_round_active_ && num_mavlink2_sinks == 0) mavlink2_round_active_ = false;
    if (gdl90_round_active_ && num_gdl90_sinks == 0) gdl90_round_active_ = false;

    bool all_locally_decoded_done =
        !csbee_round_active_ && !mavlink1_round_active_ && !mavlink2_round_active_ && !gdl90_round_active_;
    bool any_locally_decoded_active =
        (num_csbee_sinks > 0 || num_mavlink1_sinks > 0 || num_mavlink2_sinks > 0 || num_gdl90_sinks > 0);

    if (any_locally_decoded_active && all_locally_decoded_done &&
        timestamp_ms - last_locally_decoded_report_timestamp_ms_ >= kCSBeeReportingIntervalMs) {
        last_locally_decoded_report_timestamp_ms_ = timestamp_ms;
        csbee_overrun_reported_ = false;
        mavlink1_overrun_reported_ = false;
        mavlink2_overrun_reported_ = false;
        gdl90_overrun_reported_ = false;

        // Snapshot current aircraft UIDs. All protocols will walk this same array.
        report_uids_count_ = 0;
        for (auto& itr : aircraft_dictionary.dict) {
            if (report_uids_count_ < kMaxReportUIDs) {
                report_uids_[report_uids_count_++] = itr.first;
            }
        }
        csbee_report_uid_index_ = 0;
        mavlink1_report_uid_index_ = 0;
        mavlink2_report_uid_index_ = 0;
        gdl90_report_uid_index_ = 0;

        // Activate rounds for protocols that currently have sinks.
        csbee_round_active_ = (num_csbee_sinks > 0);
        mavlink1_round_active_ = (num_mavlink1_sinks > 0);
        mavlink2_round_active_ = (num_mavlink2_sinks > 0);
        gdl90_round_active_ = (num_gdl90_sinks > 0);
    }

    // Drive each in-progress reporting round. Log overrun once per round if the interval lapses.
    uint32_t elapsed_ms = timestamp_ms - last_locally_decoded_report_timestamp_ms_;
    if (csbee_round_active_) {
        if (!csbee_overrun_reported_ && elapsed_ms >= kCSBeeReportingIntervalMs) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "CSBee reporting overran the %lums reporting interval.",
                          kCSBeeReportingIntervalMs);
            csbee_overrun_reported_ = true;
        }
        if (!ReportCSBee(csbee_sinks, num_csbee_sinks)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportCSBee.");
            ret = false;
        }
    }
    if (mavlink1_round_active_) {
        if (!mavlink1_overrun_reported_ && elapsed_ms >= kMAVLINKReportingIntervalMs) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "MAVLINK1 reporting overran the %lums reporting interval.",
                          kMAVLINKReportingIntervalMs);
            mavlink1_overrun_reported_ = true;
        }
        if (!ReportMAVLINK(mavlink1_sinks, num_mavlink1_sinks, 1)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportMAVLINK with MAVLINK1 sinks.");
            ret = false;
        }
    }
    if (mavlink2_round_active_) {
        if (!mavlink2_overrun_reported_ && elapsed_ms >= kMAVLINKReportingIntervalMs) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "MAVLINK2 reporting overran the %lums reporting interval.",
                          kMAVLINKReportingIntervalMs);
            mavlink2_overrun_reported_ = true;
        }
        if (!ReportMAVLINK(mavlink2_sinks, num_mavlink2_sinks, 2)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportMAVLINK with MAVLINK2 sinks.");
            ret = false;
        }
    }
    if (gdl90_round_active_) {
        if (!gdl90_overrun_reported_ && elapsed_ms >= kGDL90ReportingIntervalMs) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "GDL90 reporting overran the %lums reporting interval.",
                          kGDL90ReportingIntervalMs);
            gdl90_overrun_reported_ = true;
        }
        if (!ReportGDL90(gdl90_sinks, num_gdl90_sinks)) {
            CONSOLE_ERROR("CommsManager::UpdateReporting", "Error during ReportGDL90.");
            ret = false;
        }
    }

    return ret;
}

bool CommsManager::ReportRaw(ReportSink* sinks, uint16_t num_sinks, const CompositeArray::RawPackets& packets) {
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
            ret &= SendBuf(sinks[j], (char*)raw_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        char raw_frame_buf[kRawUATADSBFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATADSBFrame(packets.uat_adsb_packets[i], raw_frame_buf);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char*)raw_frame_buf, num_bytes_in_frame);
        }
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        char raw_frame_buf[kRawUATUplinkFrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRawUATUplinkFrame(packets.uat_uplink_packets[i], raw_frame_buf);
        for (uint16_t j = 0; j < num_sinks; j++) {
            ret &= SendBuf(sinks[j], (char*)raw_frame_buf, num_bytes_in_frame);
        }
    }
    return ret;
}

bool CommsManager::ReportBeast(ReportSink* sinks, uint16_t num_sinks, const CompositeArray::RawPackets& packets,
                               SettingsManager::ReportingProtocol protocol) {
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
            ret &= SendBuf(sinks[j], (char*)beast_frame_buf, num_bytes_in_frame);
        }
    }
    if (protocol != SettingsManager::kBeastNoUAT) {
        for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
            uint8_t beast_frame_buf[BeastReporter::kUATADSBBeastFrameMaxLenBytes];
            uint16_t num_bytes_in_frame =
                BeastReporter::BuildUATADSBBeastFrame(beast_frame_buf, packets.uat_adsb_packets[i]);

            for (uint16_t j = 0; j < num_sinks; j++) {
                ret &= SendBuf(sinks[j], (char*)beast_frame_buf, num_bytes_in_frame);
            }
        }
    }
    if (protocol != SettingsManager::kBeastNoUATUplink && protocol != SettingsManager::kBeastNoUAT) {
        for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
            uint8_t beast_frame_buf[BeastReporter::kUATUplinkBeastFrameMaxLenBytes];
            uint16_t num_bytes_in_frame =
                BeastReporter::BuildUATUplinkBeastFrame(beast_frame_buf, packets.uat_uplink_packets[i]);
            for (uint16_t j = 0; j < num_sinks; j++) {
                ret &= SendBuf(sinks[j], (char*)beast_frame_buf, num_bytes_in_frame);
            }
        }
    }

    return ret;
}

bool CommsManager::ReportCSBee(ReportSink* sinks, uint16_t num_sinks) {
    bool ret = true;

    // Process aircraft within the time budget.
    uint32_t chunk_start_ms = get_time_since_boot_ms();
    while (csbee_report_uid_index_ < report_uids_count_) {
        if (get_time_since_boot_ms() - chunk_start_ms >= kCSBeeChunkBudgetMs) {
            return ret;  // Budget exhausted; resume on next UpdateReporting tick.
        }

        uint32_t uid = report_uids_[csbee_report_uid_index_++];

        auto itr = aircraft_dictionary.dict.find(uid);
        if (itr == aircraft_dictionary.dict.end()) {
            continue;  // Aircraft pruned mid-round; skip without losing remaining entries.
        }

        char message[kCSBeeMessageStrMaxLen];
        int message_len_bytes = -1;

        if (ModeSAircraft* mode_s_aircraft = get_if<ModeSAircraft>(&(itr->second)); mode_s_aircraft) {
            message_len_bytes = WriteCSBeeModeSAircraftMessageStr(message, *mode_s_aircraft);
        } else if (UATAircraft* uat_aircraft = get_if<UATAircraft>(&(itr->second)); uat_aircraft) {
            message_len_bytes = WriteCSBeeUATAircraftMessageStr(message, *uat_aircraft);
        } else {
            CONSOLE_WARNING("CommsManager::ReportCSBee", "Unknown aircraft type in dictionary for UID 0x%lx.", uid);
            continue;
        }

        if (message_len_bytes < 0) {
            CONSOLE_ERROR("CommsManager::ReportCSBee",
                          "Error in WriteCSBeeAircraftMessageStr for UID 0x%lx, error code %d.", uid,
                          message_len_bytes);
            ret = false;
            continue;  // Log error but do not abort the round; remaining aircraft still need reporting.
        }

        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], message, message_len_bytes);
        }
    }

    // All UIDs in the snapshot have been processed — send the statistics footer.
    char stats_message[kCSBeeMessageStrMaxLen];
    int16_t stats_len_bytes = WriteCSBeeStatisticsMessageStr(
        stats_message,
        aircraft_dictionary.metrics.demods_1090,                     // DPS
        aircraft_dictionary.metrics.raw_squitter_frames,             // RAW_SFPS
        aircraft_dictionary.metrics.valid_squitter_frames,           // SFPS
        aircraft_dictionary.metrics.raw_extended_squitter_frames,    // RAW_ESFPS
        aircraft_dictionary.metrics.valid_extended_squitter_frames,  // ESFPS
        aircraft_dictionary.metrics.raw_uat_adsb_frames + aircraft_dictionary.metrics.raw_uat_uplink_frames,  // RAW_UAT
        aircraft_dictionary.metrics.valid_uat_adsb_frames +
            aircraft_dictionary.metrics.valid_uat_uplink_frames,  // VALID_UAT
        aircraft_dictionary.GetNumAircraft(),                     // NUM_AIRCRAFT
        0u,                                                       // TSCAL
        get_time_since_boot_ms() / 1000                           // UPTIME
    );
    if (stats_len_bytes < 0) {
        CONSOLE_ERROR("CommsManager::ReportCSBee",
                      "Encountered an error in WriteCSBeeStatisticsMessageStr, error code %d.", stats_len_bytes);
        ret = false;
    } else {
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], stats_message, stats_len_bytes);
        }
    }

    csbee_round_active_ = false;
    return ret;
}

bool CommsManager::ReportMAVLINK(ReportSink* sinks, uint16_t num_sinks, uint8_t mavlink_version) {
    if (num_sinks == 0) {
        CONSOLE_WARNING("CommsManager::ReportMAVLINK", "No MAVLINK sinks provided.");
        return false;
    }
    if (mavlink_version != 1 && mavlink_version != 2) {
        CONSOLE_ERROR("CommsManager::ReportMAVLINK", "MAVLINK version %d does not exist.", mavlink_version);
        return false;
    }

    uint16_t& uid_index = (mavlink_version == 1) ? mavlink1_report_uid_index_ : mavlink2_report_uid_index_;
    bool& round_active = (mavlink_version == 1) ? mavlink1_round_active_ : mavlink2_round_active_;

    // Always refresh the protocol version before any send (idempotent).
    for (uint16_t i = 0; i < num_sinks; i++) {
        mavlink_set_proto_version(sinks[i], mavlink_version);
    }

    // Send the HEARTBEAT once at the start of each round.
    if (uid_index == 0) {
        mavlink_heartbeat_t heartbeat_msg = {.custom_mode = 0,
                                             .type = MAV_TYPE_ADSB,
                                             .autopilot = MAV_AUTOPILOT_INVALID,
                                             .base_mode = 0,
                                             .system_status = MAV_STATE_ACTIVE,
                                             .mavlink_version = mavlink_version};
        for (uint16_t i = 0; i < num_sinks; i++) {
            mavlink_msg_heartbeat_send_struct(static_cast<mavlink_channel_t>(sinks[i]), &heartbeat_msg);
        }
    }

    // Send an ADSB_VEHICLE message for each aircraft within the time budget.
    uint32_t chunk_start_ms = get_time_since_boot_ms();
    while (uid_index < report_uids_count_) {
        if (get_time_since_boot_ms() - chunk_start_ms >= kMAVLINKChunkBudgetMs) {
            return true;  // Budget exhausted; resume on next UpdateReporting tick.
        }

        uint32_t uid = report_uids_[uid_index++];

        auto itr = aircraft_dictionary.dict.find(uid);
        if (itr == aircraft_dictionary.dict.end()) {
            continue;  // Aircraft pruned mid-round; skip without losing remaining entries.
        }

        mavlink_adsb_vehicle_t adsb_vehicle_msg;
        if (ModeSAircraft* mode_s_aircraft = get_if<ModeSAircraft>(&(itr->second)); mode_s_aircraft) {
            adsb_vehicle_msg = ModeSAircraftToMAVLINKADSBVehicleMessage(*mode_s_aircraft);
        } else if (UATAircraft* uat_aircraft = get_if<UATAircraft>(&(itr->second)); uat_aircraft) {
            adsb_vehicle_msg = UATAircraftToMAVLINKADSBVehicleMessage(*uat_aircraft);
        } else {
            CONSOLE_WARNING("CommsManager::ReportMAVLINK", "Unknown aircraft type in dictionary for UID 0x%lx.", uid);
            continue;
        }
        for (uint16_t i = 0; i < num_sinks; i++) {
            mavlink_msg_adsb_vehicle_send_struct(static_cast<mavlink_channel_t>(sinks[i]), &adsb_vehicle_msg);
        }
    }

    // All UIDs processed — send the delimiter and mark this version's round complete.
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
            round_active = false;
            return false;
    }

    round_active = false;
    return true;
}

bool CommsManager::ReportGDL90(ReportSink* sinks, uint16_t num_sinks) {
    bool ret = true;

    uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
    uint16_t msg_len;

    // Send the HEARTBEAT and OWNSHIP REPORT once at the start of each round.
    if (gdl90_report_uid_index_ == 0) {
        msg_len = gdl90.WriteGDL90HeartbeatMessage(buf, sizeof(buf), get_time_since_boot_ms() / 1000,
                                                   aircraft_dictionary.metrics.valid_squitter_frames +
                                                       aircraft_dictionary.metrics.valid_extended_squitter_frames +
                                                       aircraft_dictionary.metrics.valid_uat_adsb_frames,
                                                   aircraft_dictionary.metrics.valid_uat_uplink_frames);
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], (char*)buf, msg_len);
        }

        GDL90Reporter::GDL90TargetReportData ownship_data;
        // TODO: Actually fill out ownship data!
        msg_len = gdl90.WriteGDL90TargetReportMessage(buf, sizeof(buf), ownship_data, true);
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], (char*)buf, msg_len);
        }
    }

    // Send a traffic report for each aircraft within the time budget.
    uint32_t chunk_start_ms = get_time_since_boot_ms();
    while (gdl90_report_uid_index_ < report_uids_count_) {
        if (get_time_since_boot_ms() - chunk_start_ms >= kGDL90ChunkBudgetMs) {
            return ret;  // Budget exhausted; resume on next UpdateReporting tick.
        }

        uint32_t uid = report_uids_[gdl90_report_uid_index_++];

        auto itr = aircraft_dictionary.dict.find(uid);
        if (itr == aircraft_dictionary.dict.end()) {
            continue;  // Aircraft pruned mid-round; skip without losing remaining entries.
        }

        msg_len = 0;
        if (ModeSAircraft* mode_s_aircraft = get_if<ModeSAircraft>(&(itr->second)); mode_s_aircraft) {
            msg_len = gdl90.WriteGDL90TargetReportMessage(buf, sizeof(buf), *mode_s_aircraft, false);
        } else if (UATAircraft* uat_aircraft = get_if<UATAircraft>(&(itr->second)); uat_aircraft) {
            msg_len = gdl90.WriteGDL90TargetReportMessage(buf, sizeof(buf), *uat_aircraft, false);
        } else {
            CONSOLE_WARNING("CommsManager::ReportGDL90", "Unknown aircraft type in dictionary for UID 0x%lx.", uid);
            continue;
        }
        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], (char*)buf, msg_len);
        }
    }

    gdl90_round_active_ = false;
    return ret;
}

bool CommsManager::ReportGDL90Uplink(ReportSink* sinks, uint16_t num_sinks, const CompositeArray::RawPackets& packets) {
    bool ret = true;

    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        // We need to decode the packet since GDL90 expects just the decoded payload. This double decoding is a bit
        // wasteful but lets us use a common interface for reporting raw packets, instead of requiring decoded UAT
        // uplink packets to be passed into special snowflake GDL90 reporting functions.
        DecodedUATUplinkPacket packet = DecodedUATUplinkPacket(packets.uat_uplink_packets[i]);
        if (!packet.is_valid) {
            CONSOLE_WARNING("CommsManager::ReportGDL90Uplink", "Invalid UAT uplink packet encountered, skipping.");
            continue;
        }
        uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
        uint16_t msg_len = gdl90.WriteGDL90UplinkDataMessage(
            buf, sizeof(buf), packet.decoded_payload, DecodedUATUplinkPacket::kDecodedPayloadNumBytes,
            GDL90Reporter::MLAT48MHz64BitCountsToUATTORTicks(packet.raw.mlat_48mhz_64bit_counts));

        for (uint16_t i = 0; i < num_sinks; i++) {
            ret &= SendBuf(sinks[i], (char*)buf, msg_len);
        }
    }
    return ret;
}