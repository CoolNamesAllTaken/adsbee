#include "adsbee.hh"
#include "beast_utils.hh"
#include "comms.hh"
#include "composite_array.hh"
#include "csbee_utils.hh"
#include "gdl90_utils.hh"
#include "hal.hh"  // For timestamping.
#include "mavlink_utils.hh"
#include "raw_utils.hh"
#include "spi_coprocessor.hh"
#include "unit_conversions.hh"

static constexpr uint16_t kMaxNumModeSPacketsToReport = 100;
static constexpr uint16_t kMaxNumUATADSBPacketsToReport = 50;
static constexpr uint16_t kMaxNumUATUplinkPacketsToReport = 2;

extern ADSBee adsbee;

bool CommsManager::UpdateReporting() {
    bool ret = true;
    uint32_t timestamp_ms = get_time_since_boot_ms();

    if (timestamp_ms - last_raw_report_timestamp_ms_ <= kRawReportingIntervalMs) {
        return true;  // Nothing to update.
    }
    // Proceed with update and record timestamp.
    last_raw_report_timestamp_ms_ = timestamp_ms;

    uint8_t packet_array_buf[SPICoprocessorPacket::SCResponsePacket::kDataMaxLenBytes] = {0};

    CompositeArray::RawPackets packets_to_report =
        CompositeArray::PackRawPacketsBuffer(packet_array_buf, sizeof(packet_array_buf), &mode_s_packet_reporting_queue,
                                             &uat_adsb_packet_reporting_queue, &uat_uplink_packet_reporting_queue);

    // Forward the CompositeArray::RawPackets to the ESP32 if enabled.
    if (esp32.IsEnabled() && packets_to_report.IsValid()) {
        // Write packet to ESP32 with a forced ACK.
        esp32.Write(ObjectDictionary::kAddrCompositeArrayRawPackets,  // addr
                    packet_array_buf,                                 // buf
                    true,                                             // require_ack
                    packets_to_report.len_bytes                       // len
        );
    }

    bool csbee_report_needed, mavlink_report_needed, gdl90_report_needed = false;
    if (timestamp_ms - last_csbee_report_timestamp_ms_ >= kCSBeeReportingIntervalMs) {
        csbee_report_needed = true;
        last_csbee_report_timestamp_ms_ = timestamp_ms;
    }
    if (timestamp_ms - last_mavlink_report_timestamp_ms_ >= kMAVLINKReportingIntervalMs) {
        mavlink_report_needed = true;
        last_mavlink_report_timestamp_ms_ = timestamp_ms;
    }
    if (timestamp_ms - last_gdl90_report_timestamp_ms_ >= kGDL90ReportingIntervalMs) {
        gdl90_report_needed = true;
        last_gdl90_report_timestamp_ms_ = timestamp_ms;
    }

    // TODO: Refactor this so that each report function takes an array of relevant ReportSinks, so we only generate the
    // reporting output for each protocol once per update step.
    for (uint16_t i = 0; i < SettingsManager::SerialInterface::kGNSSUART; i++) {
        SettingsManager::SerialInterface iface = static_cast<SettingsManager::SerialInterface>(i);
        switch (settings_manager.settings.reporting_protocols[i]) {
            case SettingsManager::kNoReports:
                break;
            case SettingsManager::kRaw:
                ret = ReportRaw(iface, packets_to_report);
                break;
            case SettingsManager::kBeast:
                ret = ReportBeast(iface, packets_to_report);
                break;
            case SettingsManager::kCSBee:
                if (csbee_report_needed) {
                    ret = ReportCSBee(iface);
                }
                break;
            case SettingsManager::kMAVLINK1:
            case SettingsManager::kMAVLINK2:
                if (mavlink_report_needed) {
                    ret = ReportMAVLINK(iface);
                }
                break;
            case SettingsManager::kGDL90:
                if (gdl90_report_needed) {
                    ret = ReportGDL90(iface);
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
