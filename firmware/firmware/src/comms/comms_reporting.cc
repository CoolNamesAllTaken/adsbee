#include "ads_bee.hh"
#include "comms.hh"

extern ADSBee ads_bee;

bool CommsManager::InitReporting() { return true; }

bool CommsManager::UpdateReporting() {
    for (uint16_t iface = 0; iface < SerialInterface::kGNSSUART; iface++) {
        switch (reporting_protocols_[iface]) {
            case kNone:
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
                CONSOLE_PRINTF("Invalid reporting protocol %d specified for interface %d.\r\n",
                               reporting_protocols_[iface], iface);
                return false;
                break;
        }
    }
    return true;
}

bool CommsManager::ReportMAVLINK(SerialInterface iface) { ads_bee.aircraft_dictionary. }