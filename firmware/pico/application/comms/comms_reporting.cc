#include "adsbee.hh"
#include "beast_utils.hh"
#include "comms.hh"
#include "csbee_utils.hh"
#include "gdl90_utils.hh"
#include "hal.hh"  // For timestamping.
#include "mavlink_utils.hh"
#include "raw_utils.hh"
#include "spi_coprocessor.hh"
#include "unit_conversions.hh"

extern ADSBee adsbee;

GDL90Reporter gdl90;

bool CommsManager::InitReporting() { return true; }

bool CommsManager::UpdateReporting() {
    bool ret = true;
    uint32_t timestamp_ms = get_time_since_boot_ms();

    if (timestamp_ms - last_raw_report_timestamp_ms_ <= kRawReportingIntervalMs) {
        return true;  // Nothing to update.
    }
    // Proceed with update and record timestamp.
    last_raw_report_timestamp_ms_ = timestamp_ms;

    DecodedModeSPacket packets_to_report[SettingsManager::Settings::kMaxNumTransponderPackets];
    /**
     * Raw packet reporting buffer used to transfer multiple packets at once over SPI.
     * [<uint8_t num_packets to report> <packet 1> <packet 2> ...]
     */
    uint8_t spi_raw_packet_reporting_buffer[sizeof(uint8_t) + SettingsManager::Settings::kMaxNumTransponderPackets];

    // Fill up the array of DecodedModeSPackets for internal functions, and the buffer of RawModeSPackets to
    // send to the ESP32 over SPI. RawModeSPackets are used instead of DecodedModeSPackets over the SPI link
    // in order to preserve bandwidth.
    uint16_t num_packets_to_report = 0;
    for (; num_packets_to_report < SettingsManager::Settings::kMaxNumTransponderPackets &&
           transponder_packet_reporting_queue.Dequeue(packets_to_report[num_packets_to_report]);
         num_packets_to_report++) {
        if (esp32.IsEnabled()) {
            // Dequeue all the packets to report (up to max limit of the buffer).
            RawModeSPacket raw_packet = packets_to_report[num_packets_to_report].GetRaw();
            spi_raw_packet_reporting_buffer[0] = num_packets_to_report + 1;
            memcpy(spi_raw_packet_reporting_buffer + sizeof(uint8_t) + sizeof(RawModeSPacket) * num_packets_to_report,
                   &raw_packet, sizeof(RawModeSPacket));
        }
    }
    if (esp32.IsEnabled() && num_packets_to_report > 0) {
        // Write packet to ESP32 with a forced ACK.
        esp32.Write(ObjectDictionary::kAddrRawModeSPacketArray,                       // addr
                    spi_raw_packet_reporting_buffer,                                  // buf
                    true,                                                             // require_ack
                    sizeof(uint8_t) + num_packets_to_report * sizeof(RawModeSPacket)  // len
        );
    }

    for (uint16_t i = 0; i < SettingsManager::SerialInterface::kGNSSUART; i++) {
        SettingsManager::SerialInterface iface = static_cast<SettingsManager::SerialInterface>(i);
        switch (settings_manager.settings.reporting_protocols[i]) {
            case SettingsManager::kNoReports:
                break;
            case SettingsManager::kRaw:
                ret = ReportRaw(iface, packets_to_report, num_packets_to_report);
                break;
            case SettingsManager::kBeast:
                ret = ReportBeast(iface, packets_to_report, num_packets_to_report);
                break;
            case SettingsManager::kCSBee:
                if (timestamp_ms - last_csbee_report_timestamp_ms_ >= kCSBeeReportingIntervalMs) {
                    ret = ReportCSBee(iface);
                    last_csbee_report_timestamp_ms_ = timestamp_ms;
                }
                break;
            case SettingsManager::kMAVLINK1:
            case SettingsManager::kMAVLINK2:
                if (timestamp_ms - last_mavlink_report_timestamp_ms_ >= kMAVLINKReportingIntervalMs) {
                    ret = ReportMAVLINK(iface);
                    last_mavlink_report_timestamp_ms_ = timestamp_ms;
                }
                break;
            case SettingsManager::kGDL90:
                if (timestamp_ms - last_gdl90_report_timestamp_ms_ >= kGDL90ReportingIntervalMs) {
                    ret = ReportGDL90(iface);
                    last_gdl90_report_timestamp_ms_ = timestamp_ms;
                }
                break;
            case SettingsManager::kNumProtocols:
            default:
                CONSOLE_WARNING("CommsManager::UpdateReporting",
                                "Invalid reporting protocol %d specified for interface %d.",
                                settings_manager.settings.reporting_protocols[i], i);
                ret = false;
                break;
        }
    }

    return ret;
}

bool CommsManager::ReportRaw(SettingsManager::SerialInterface iface, const DecodedModeSPacket packets_to_report_1090[],
                             uint16_t num_packets_to_report) {
    for (uint16_t i = 0; i < num_packets_to_report; i++) {
        char raw_frame_buf[kRaw1090FrameMaxNumChars];
        uint16_t num_bytes_in_frame = BuildRaw1090Frame(packets_to_report_1090[i].GetRaw(), raw_frame_buf);
        SendBuf(iface, (char *)raw_frame_buf, num_bytes_in_frame);
        comms_manager.iface_puts(iface, (char *)"\r\n");  // Send delimiter.
    }
    return true;
}

bool CommsManager::ReportBeast(SettingsManager::SerialInterface iface,
                               const DecodedModeSPacket packets_to_report_1090[], uint16_t num_packets_to_report) {
    for (uint16_t i = 0; i < num_packets_to_report; i++) {
        uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];
        uint16_t num_bytes_in_frame = Build1090BeastFrame(packets_to_report_1090[i], beast_frame_buf);
        comms_manager.iface_putc(iface, char(0x1a));  // Send beast escape char to denote beginning of frame.
        SendBuf(iface, (char *)beast_frame_buf, num_bytes_in_frame);
    }
    return true;
}

bool CommsManager::ReportCSBee(SettingsManager::SerialInterface iface) {
    // Write out a CSBee Aircraft message for each aircraft in the aircraft dictionary.
    for (auto &itr : adsbee.aircraft_dictionary.dict) {
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
        SendBuf(iface, message, message_len_bytes);
    }

    // Write a CSBee Statistics message.
    char message[kCSBeeMessageStrMaxLen];
    int16_t message_len_bytes =
        WriteCSBeeStatisticsMessageStr(message,                                                 // Buffer to write into.
                                       adsbee.aircraft_dictionary.metrics.demods_1090,          // DPS
                                       adsbee.aircraft_dictionary.metrics.raw_squitter_frames,  // RAW_SFPS
                                       adsbee.aircraft_dictionary.metrics.valid_squitter_frames,           // SFPS
                                       adsbee.aircraft_dictionary.metrics.raw_extended_squitter_frames,    // RAW_ESFPS
                                       adsbee.aircraft_dictionary.metrics.valid_extended_squitter_frames,  // ESFPS
                                       adsbee.aircraft_dictionary.metrics.raw_uat_adsb_frames,             // RAW_UAT
                                       adsbee.aircraft_dictionary.metrics.valid_uat_adsb_frames,           // VALID_UAT
                                       adsbee.aircraft_dictionary.GetNumAircraft(),  // NUM_AIRCRAFT
                                       0u,                                           // TSCAL
                                       get_time_since_boot_ms() / 1000               // UPTIME
        );
    if (message_len_bytes < 0) {
        CONSOLE_ERROR("CommsManager::ReportCSBee",
                      "Encountered an error in WriteCSBeeStatisticsMessageStr, error code %d.", message_len_bytes);
        return false;
    }
    SendBuf(iface, message, message_len_bytes);
    return true;
}

bool CommsManager::ReportMAVLINK(SettingsManager::SerialInterface iface) {
    uint8_t mavlink_version =
        settings_manager.settings.reporting_protocols[iface] == SettingsManager::kMAVLINK1 ? 1 : 2;
    mavlink_set_proto_version(SettingsManager::SerialInterface::kCommsUART, mavlink_version);

    // Send a HEARTBEAT message.
    mavlink_heartbeat_t heartbeat_msg = {.custom_mode = 0,
                                         .type = MAV_TYPE_ADSB,
                                         .autopilot = MAV_AUTOPILOT_INVALID,
                                         .base_mode = 0,
                                         .system_status = MAV_STATE_ACTIVE,
                                         .mavlink_version = mavlink_version};
    mavlink_msg_heartbeat_send_struct(static_cast<mavlink_channel_t>(iface), &heartbeat_msg);

    // Send an ADSB_VEHICLE message for each aircraft in the dictionary.
    for (auto &itr : adsbee.aircraft_dictionary.dict) {
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
        mavlink_msg_adsb_vehicle_send_struct(static_cast<mavlink_channel_t>(iface), &adsb_vehicle_msg);
    }
    // Send delimiter message.
    switch (mavlink_version) {
        case 1: {
            mavlink_request_data_stream_t request_data_stream_msg = {0};
            mavlink_msg_request_data_stream_send_struct(static_cast<mavlink_channel_t>(iface),
                                                        &request_data_stream_msg);
            break;
        }
        case 2: {
            mavlink_message_interval_t message_interval_msg = {
                .interval_us = (int32_t)(kMAVLINKReportingIntervalMs * (uint32_t)kUsPerMs),
                .message_id = MAVLINK_MSG_ID_ADSB_VEHICLE};
            mavlink_msg_message_interval_send_struct(static_cast<mavlink_channel_t>(iface), &message_interval_msg);
            break;
        }
        default:
            CONSOLE_ERROR("CommsManager::ReportMAVLINK", "MAVLINK version %d does not exist.", mavlink_version);
            return false;
    };

    return true;
}

bool CommsManager::ReportGDL90(SettingsManager::SerialInterface iface) {
    uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
    uint16_t msg_len;

    // Heartbeat Message
    msg_len = gdl90.WriteGDL90HeartbeatMessage(buf, get_time_since_boot_ms() / 1000,
                                               adsbee.aircraft_dictionary.metrics.valid_extended_squitter_frames);
    SendBuf(iface, (char *)buf, msg_len);

    // Ownship Report
    GDL90Reporter::GDL90TargetReportData ownship_data;
    // TODO: Actually fill out ownship data!
    msg_len = gdl90.WriteGDL90TargetReportMessage(buf, ownship_data, true);
    SendBuf(iface, (char *)buf, msg_len);

    // Traffic Reports
    for (auto &itr : adsbee.aircraft_dictionary.dict) {
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
        SendBuf(iface, (char *)buf, msg_len);
    }
    return true;
}