#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "esp32_flasher.hh"
#include "hal.hh"
#include "hardware_unit_tests.hh"  // For testing only!
#include "pico/binary_info.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "transponder_packet.hh"
#include "unit_conversions.hh"

const uint32_t kESP32BootupTimeoutMs = 10000;
const uint32_t kESP32BootupCommsRetryMs = 500;

ADSBee::ADSBeeConfig ads_bee_config;
// Override default config params here.
ADSBee adsbee = ADSBee(ads_bee_config);
CommsManager comms_manager = CommsManager({});
ESP32SerialFlasher esp32_flasher = ESP32SerialFlasher({});
EEPROM eeprom = EEPROM({});
SettingsManager settings_manager;
ObjectDictionary object_dictionary;
SPICoprocessor esp32 = SPICoprocessor({});

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    adsbee.Init();
    eeprom.Init();
    comms_manager.Init();
    comms_manager.iface_printf(SettingsManager::SerialInterface::kConsole,
                               "ADSBee 1090\r\nSoftware Version %d.%d.%d\r\n", object_dictionary.kFirmwareVersionMajor,
                               object_dictionary.kFirmwareVersionMinor, object_dictionary.kFirmwareVersionPatch);
    comms_manager.iface_printf(SettingsManager::SerialInterface::kCommsUART,
                               "ADSBee 1090\r\nSoftware Version %d.%d.%d\r\n", object_dictionary.kFirmwareVersionMajor,
                               object_dictionary.kFirmwareVersionMinor, object_dictionary.kFirmwareVersionPatch);
    comms_manager.iface_printf(SettingsManager::SerialInterface::kGNSSUART,
                               "ADSBee 1090\r\nSoftware Version %d.%d.%d\r\n", object_dictionary.kFirmwareVersionMajor,
                               object_dictionary.kFirmwareVersionMinor, object_dictionary.kFirmwareVersionPatch);

    settings_manager.Load();
    esp32.Init();

    // If WiFi is enabled, try establishing communication with the ESP32 and maybe update its firmware.
    if (comms_manager.WiFiIsEnabled()) {
        // Try reading from the ESP32 till it finishes turning on.
        uint32_t esp32_firmware_version = 0x0;
        bool flash_esp32 = true;
        uint32_t esp32_comms_start_timestamp_ms = get_time_since_boot_ms();
        uint32_t esp32_comms_last_try_timestamp_ms = 0;
        while (get_time_since_boot_ms() - esp32_comms_start_timestamp_ms < kESP32BootupTimeoutMs) {
            // Wait until the next retry interval to avoid spamming the ESP32 continuously.
            if (get_time_since_boot_ms() - esp32_comms_last_try_timestamp_ms < kESP32BootupCommsRetryMs) {
                continue;
            }
            esp32_comms_last_try_timestamp_ms = get_time_since_boot_ms();
            // Try reading the firmware version from the ESP32. If the read succeeds, confirm that the firmware
            // version matches ours.
            if (!esp32.Read(ObjectDictionary::Address::kAddrFirmwareVersion, esp32_firmware_version)) {
                CONSOLE_ERROR("main", "Unable to read firmware version from ESP32.");
            } else if (esp32_firmware_version != object_dictionary.kFirmwareVersion) {
                CONSOLE_ERROR("main",
                              "Incorrect firmware version detected on ESP32. Pico is running %d.%d.%d but ESP32 is "
                              "running %d.%d.%d",
                              object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                              object_dictionary.kFirmwareVersionPatch, esp32_firmware_version >> 16,
                              (esp32_firmware_version >> 8) & 0xFF, esp32_firmware_version & 0xFF);
            } else {
                // Firmware checks out, all good! Don't flash the ESP32.
                flash_esp32 = false;
                break;
            }
        }
        // If we never read from the ESP32, or read a different firmware version, try writing to it.
        if (flash_esp32) {
            if (!esp32.DeInit()) {
                CONSOLE_ERROR("main", "Error while de-initializing ESP32 before flashing.");
            }
            if (!esp32_flasher.FlashESP32()) {
                CONSOLE_ERROR("main", "Error while flashing ESP32.");
            }
            if (!esp32.Init()) {
                CONSOLE_ERROR("main", "Error while re-initializing ESP32 after flashing.");
            }
        }
    }

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
    test_aircraft.track_deg = 100;
    test_aircraft.velocity_kts = 200;
    adsbee.aircraft_dictionary.InsertAircraft(test_aircraft);

    // int argc = 0;
    // const char* argv[1];
    // utest_main(argc, argv);

    uint16_t esp32_test_packet_interval_ms = 1000;
    uint32_t esp32_test_packet_last_sent_timestamp_ms = get_time_since_boot_ms();

    while (true) {
        // Send test packet to ESP32.
        uint32_t esp32_test_packet_timestamp_ms = get_time_since_boot_ms();
        if (esp32_test_packet_timestamp_ms - esp32_test_packet_last_sent_timestamp_ms > esp32_test_packet_interval_ms) {
            RawTransponderPacket test_packet =
                RawTransponderPacket((char*)"8dac009458b9970f0aa394359da9", -123, 456789);
            esp32.Write(ObjectDictionary::kAddrRawTransponderPacket, test_packet, true);
            CONSOLE_INFO("Debug", "Sent ESP32 message.");
            esp32_test_packet_last_sent_timestamp_ms = esp32_test_packet_timestamp_ms;
        }

        // Loop forever.
        comms_manager.Update();
        adsbee.Update();

        if (comms_manager.WiFiIsEnabled()) {
            esp32.Update();
        }
    }
}