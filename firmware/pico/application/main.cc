#include <mutex>

#include "adsbee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "esp32_flasher.hh"
#include "firmware_update.hh"  // For figuring out which flash partition we're in.
#include "hal.hh"
#include "hardware_unit_tests.hh"  // For testing only!
#include "packet_decoder.hh"
#include "pico/binary_info.h"
#include "pico/multicore.h"
#include "pico/stdlib.h"
#include "spi_coprocessor.hh"
#include "transponder_packet.hh"
#include "unit_conversions.hh"

// For testing only
#include "hardware/gpio.h"

const uint16_t kStatusLEDBootupBlinkPeriodMs = 200;
const uint32_t kESP32BootupTimeoutMs = 10000;
const uint32_t kESP32BootupCommsRetryMs = 500;

const uint32_t kMultiCoreStartHandshake = 0x12345678;

// Override default config params here.
ADSBee adsbee = ADSBee({});
CommsManager comms_manager = CommsManager({});
ESP32SerialFlasher esp32_flasher = ESP32SerialFlasher({});
EEPROM eeprom = EEPROM({});
SettingsManager settings_manager;
ObjectDictionary object_dictionary;
SPICoprocessor esp32 = SPICoprocessor({});
PacketDecoder decoder = PacketDecoder({.enable_1090_error_correction = true});

void main_core1() {
    while (true) {
        decoder.UpdateDecoderLoop();
    }
}

int main() {
    bi_decl(bi_program_description("ADSBee 1090 ADSB Receiver"));

    eeprom.Init();
    adsbee.Init();
    comms_manager.Init();
    comms_manager.console_printf("ADSBee 1090\r\nSoftware Version %d.%d.%d\r\n",
                                 object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                                 object_dictionary.kFirmwareVersionPatch);

    settings_manager.Load();

    uint16_t num_status_led_blinks = FirmwareUpdateManager::AmWithinFlashPartition(0) ? 1 : 2;
    // Blink the LED a few times to indicate a successful startup.
    for (uint16_t i = 0; i < num_status_led_blinks; i++) {
        adsbee.SetStatusLED(true);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
        adsbee.SetStatusLED(false);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
    }

    // If WiFi is enabled, try establishing communication with the ESP32 and maybe update its firmware.
    if (esp32.IsEnabled()) {
        adsbee.DisableWatchdog();  // Disable watchdog while setting up ESP32, in case kESP32BootupTimeoutMs >=
                                   // watchdog timeout, and to avoid watchdog reboot during ESP32 programming.

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
                // Couldn't read firmware version from ESP32. Try again later.
                CONSOLE_ERROR("main", "Unable to read firmware version from ESP32.");
            } else if (esp32_firmware_version != object_dictionary.kFirmwareVersion) {
                // ESP32 firmware version doesn't match ours. Flash the ESP32.
                CONSOLE_ERROR("main",
                              "Incorrect firmware version detected on ESP32. Pico is running %d.%d.%d but ESP32 is "
                              "running %d.%d.%d",
                              object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                              object_dictionary.kFirmwareVersionPatch, esp32_firmware_version >> 16,
                              (esp32_firmware_version >> 8) & 0xFF, esp32_firmware_version & 0xFF);
                break;
            } else {
                // Firmware checks out, all good! Don't flash the ESP32.
                flash_esp32 = false;
                break;
            }
        }
        adsbee.EnableWatchdog();  // Restore watchdog.
        // If we never read from the ESP32, or read a different firmware version, try writing to it.
        if (flash_esp32) {
            adsbee.DisableWatchdog();  // Disable watchdog while flashing.
            if (!esp32.DeInit()) {
                CONSOLE_ERROR("main", "Error while de-initializing ESP32 before flashing.");
            } else if (!esp32_flasher.FlashESP32()) {
                CONSOLE_ERROR("main", "Error while flashing ESP32.");
            } else if (!esp32.Init()) {
                CONSOLE_ERROR("main", "Error while re-initializing ESP32 after flashing.");
            }
            adsbee.EnableWatchdog();  // Restore watchdog after flashing.
        }
    }

    multicore_reset_core1();
    multicore_launch_core1(main_core1);

    // Add a test aircraft to start.
    // Aircraft test_aircraft;
    // test_aircraft.category = Aircraft::Category::kCategorySpaceTransatmosphericVehicle;
    // strcpy(test_aircraft.callsign, "TST1234");
    // test_aircraft.latitude_deg = 20;
    // test_aircraft.longitude_deg = -140;
    // test_aircraft.baro_altitude_ft = 10000;
    // test_aircraft.vertical_rate_fpm = -5;
    // test_aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
    // test_aircraft.direction_deg = 100;
    // test_aircraft.velocity_kts = 200;
    // adsbee.aircraft_dictionary.InsertAircraft(test_aircraft);

    uint16_t esp32_heartbeat_interval_ms = 200;  // Set to 5Hz to make network terminal commands pass less laggy.
    uint32_t esp32_heartbeat_last_sent_timestamp_ms = get_time_since_boot_ms();

    while (true) {
        // Loop forever.
        // decoder.UpdateDecoderLoop();
        decoder.UpdateLogLoop();
        comms_manager.Update();
        adsbee.Update();

        bool esp32_heartbeat_was_acked = false;
        if (esp32.IsEnabled()) {
            // Send ESP32 heartbeat.
            uint32_t esp32_heartbeat_timestamp_ms = get_time_since_boot_ms();
            if (esp32_heartbeat_timestamp_ms - esp32_heartbeat_last_sent_timestamp_ms > esp32_heartbeat_interval_ms) {
                if (!esp32.Write(ObjectDictionary::kAddrScratch, esp32_heartbeat_timestamp_ms, true)) {
                    CONSOLE_ERROR("main", "ESP32 heartbeat failed.");
                } else {
                    esp32_heartbeat_was_acked = true;
                }

                esp32_heartbeat_last_sent_timestamp_ms = esp32_heartbeat_timestamp_ms;
            } else {
                // The heartbeat write calls Update() if the handshake line is pending, so only call Update() manually
                // if no heartbeat packet was sent.
                esp32.Update();
            }
        }

        if (!esp32.IsEnabled() || esp32_heartbeat_was_acked) {
            // Don't need to talk to the ESP32, or it acknowledged a heartbeat just now: poke the watchdog since nothing
            // seems amiss.
            adsbee.PokeWatchdog();
        }
    }
}