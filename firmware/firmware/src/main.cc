#include "ads_b_packet.hh"
#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "hal.hh"
#include "pico/binary_info.h"
#include "settings.hh"

const char* kSoftwareVersionStr = "0.0.1";

static const uint16_t kBitsPerNibble = 4;
static const uint16_t kBitsPerByte = 8;

ADSBee::ADSBeeConfig ads_bee_config;
// Override default config params here.
ADSBee ads_bee = ADSBee(ads_bee_config);
CommsManager comms_manager = CommsManager({});
EEPROM eeprom = EEPROM({});
SettingsManager settings_manager;

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    ads_bee.Init();
    eeprom.Init();
    comms_manager.Init();
    comms_manager.iface_printf(CommsManager::SerialInterface::kConsole, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);
    comms_manager.iface_printf(CommsManager::SerialInterface::kCommsUART, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);
    comms_manager.iface_printf(CommsManager::SerialInterface::kGNSSUART, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);

    // Add a test aircraft to start.
    // TODO: Remove this.
    Aircraft test_aircraft;
    test_aircraft.airframe_type = Aircraft::AirframeType::kAirframeTypeSpaceTransatmosphericVehicle;
    test_aircraft.latitude_deg = 20;
    test_aircraft.longitude_deg = -140;
    test_aircraft.baro_altitude_ft = 10000;
    test_aircraft.vertical_rate_fpm = -5;
    test_aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
    test_aircraft.heading_deg = 100;
    test_aircraft.velocity_kts = 200;
    ads_bee.aircraft_dictionary.InsertAircraft(test_aircraft);

    while (true) {
        // Loop forever.
        comms_manager.Update();
        ads_bee.Update();

        TransponderPacket packet;
        while (ads_bee.transponder_packet_queue.Pop(packet)) {
            uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];
            packet.DumpPacketBuffer(packet_buffer);
            if (packet.GetPacketBufferLenBits() == TransponderPacket::kExtendedSquitterPacketLenBits) {
                CONSOLE_LOG("New message: 0x%08x|%08x|%08x|%04x RSSI=%d", packet_buffer[0], packet_buffer[1],
                            packet_buffer[2], (packet_buffer[3]) >> (4 * kBitsPerNibble), packet.GetRSSIDBm());
            } else {
                CONSOLE_LOG("New message: 0x%08x|%06x RSSI=%d", packet_buffer[0],
                            (packet_buffer[1]) >> (2 * kBitsPerNibble), packet.GetRSSIDBm());
            }

            if (packet.IsValid()) {
                ads_bee.FlashStatusLED();
                CONSOLE_LOG("\tdf=%d icao_address=0x%06x", packet.GetDownlinkFormat(), packet.GetICAOAddress());
                ads_bee.aircraft_dictionary.IngestADSBPacket(ADSBPacket(packet));
                CONSOLE_LOG("\taircraft_dictionary: %d aircraft", ads_bee.aircraft_dictionary.GetNumAircraft());
            } else if (packet.GetPacketBufferLenBits() == TransponderPacket::kSquitterPacketNumBits) {
                // Marked invalid because CRC could not be confirmed. See if it's in the ICAO dictionary!
                if (ads_bee.aircraft_dictionary.ContainsAircraft(packet.GetICAOAddress())) {
                    ads_bee.FlashStatusLED();
                    CONSOLE_LOG("\tMLAT OK");
                }
                CONSOLE_LOG("INVALID %s", packet.debug_string);
            }
        }
    }
}