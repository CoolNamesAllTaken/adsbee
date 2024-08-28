#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "esp32_flasher.hh"
#include "hal.hh"
#include "pico/binary_info.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "transponder_packet.hh"
#include "unit_conversions.hh"

const char* kSoftwareVersionStr = "0.0.1";

ADSBee::ADSBeeConfig ads_bee_config;
// Override default config params here.
ADSBee ads_bee = ADSBee(ads_bee_config);
CommsManager comms_manager = CommsManager({});
ESP32SerialFlasher esp32_flasher = ESP32SerialFlasher({});
EEPROM eeprom = EEPROM({});
SettingsManager settings_manager;
SPICoprocessor esp32 = SPICoprocessor({});

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    ads_bee.Init();
    eeprom.Init();
    comms_manager.Init();
    comms_manager.iface_printf(SettingsManager::SerialInterface::kConsole, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);
    comms_manager.iface_printf(SettingsManager::SerialInterface::kCommsUART, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);
    comms_manager.iface_printf(SettingsManager::SerialInterface::kGNSSUART, "ADSBee 1090\r\nSoftware Version %s\r\n",
                               kSoftwareVersionStr);

    settings_manager.Load();
    esp32.Init();

    // Add a test aircraft to start.
    // TODO: Remove this.
    Aircraft test_aircraft;
    test_aircraft.airframe_type = Aircraft::AirframeType::kAirframeTypeSpaceTransatmosphericVehicle;
    strcpy(test_aircraft.callsign, "TST1234");
    test_aircraft.latitude_deg = 20;
    test_aircraft.longitude_deg = -140;
    test_aircraft.baro_altitude_ft = 10000;
    test_aircraft.vertical_rate_fpm = -5;
    test_aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
    test_aircraft.heading_deg = 100;
    test_aircraft.velocity_kts = 200;
    ads_bee.aircraft_dictionary.InsertAircraft(test_aircraft);

    uint16_t esp32_test_packet_interval_ms = 1000;
    uint32_t esp32_test_packet_last_sent_timestamp_ms = get_time_since_boot_ms();

    while (true) {
        // Send test packet to ESP32.
        uint32_t esp32_test_packet_timestamp_ms = get_time_since_boot_ms();
        if (esp32_test_packet_timestamp_ms - esp32_test_packet_last_sent_timestamp_ms > esp32_test_packet_interval_ms) {
            RawTransponderPacket test_packet =
                RawTransponderPacket((char*)"8dac009458b9970f0aa394359da9", -123, 456789);
            SPICoprocessor::RawTransponderPacketMessage message =
                SPICoprocessor::RawTransponderPacketMessage(test_packet);
            CONSOLE_INFO("Debug", "Sent ESP32 message.");
            esp32.SendMessage(message);
            esp32_test_packet_last_sent_timestamp_ms = esp32_test_packet_timestamp_ms;
        }

        // Loop forever.
        comms_manager.Update();
        ads_bee.Update();
    }
}