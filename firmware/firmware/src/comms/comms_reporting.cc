#include "ads_bee.hh"
#include "comms.hh"
#include "mavlink/mavlink.h"

extern ADSBee ads_bee;

bool CommsManager::InitReporting() { return true; }

bool CommsManager::UpdateReporting() {
    for (uint16_t iface = 0; iface < SerialInterface::kGNSSUART; iface++) {
        switch (reporting_protocols_[iface]) {
            case kNoReports:
                break;
            case kRaw:
                break;
            case kRawValidated:
                break;
            case kMAVLINK:
                break;
            case kGDL90:
                // Currently not supported.
                break;
            case kNumProtocols:
            default:
                CONSOLE_WARNING("Invalid reporting protocol %d specified for interface %d.",
                                reporting_protocols_[iface], iface);
                return false;
                break;
        }
    }
    return true;
}

bool CommsManager::ReportMAVLINK(SerialInterface iface) {
    for (auto &itr : ads_bee.aircraft_dictionary.dict) {
        const Aircraft &aircraft = itr.second;

        // Initialize the message
        mavlink_adsb_vehicle_t adsb_vehicle_msg = {
            .ICAO_address = aircraft.icao_address,
            .lat = static_cast<int32_t>(aircraft.latitude_deg * 1e7f),
            .lon = static_cast<int32_t>(aircraft.longitude_deg * 1e7f),
            .altitude = aircraft.barometric_altitude_m,

        };
    }
    return true;
}