#include <mutex>

#include "adsbee.hh"
#include "comms.hh"
#include "core1.hh"  // Functions for runningon core1.
#include "cpu_utils.hh"
#include "eeprom.hh"
#include "esp32.hh"
#include "esp32_flasher.hh"
#include "firmware_update.hh"  // For figuring out which flash partition we're in.
#include "hal.hh"
#include "hardware_unit_tests.hh"  // For testing only!
#include "mode_s_packet.hh"
#include "mode_s_packet_decoder.hh"
#include "pico/binary_info.h"
#include "pico/stdlib.h"
#include "spi_coprocessor.hh"
#include "unit_conversions.hh"

// #define DEBUG_DISABLE_ESP32_FLASH  // Uncomment this to stop the RP2040 from flashing the ESP32.

// For testing only
#include "hardware/gpio.h"

const uint16_t kStatusLEDBootupBlinkPeriodMs = 200;
const uint32_t kESP32BootupTimeoutMs = 2000;
const uint32_t kESP32BootupCommsRetryMs = 500;

const uint32_t kRP2040IdleTicksPerUpdateInterval =
    125e3;  // Arbitrary, assume 1000 instructions per idle loop at 125MHz.
const uint32_t kRP2040CPUMonitorUpdateIntervalMs = 1000;

// Override default config params here.
EEPROM eeprom = EEPROM({});
// BSP gets configured differently if there is or isn't an EEPROM attached. Attempt to initialize the EEPROM to figure
// out which board configuration we should load (settings in flash, or settings in EEPROM).
BSP bsp = BSP(eeprom.Init());

CPUMonitor core_0_monitor = CPUMonitor({.idle_ticks_per_update_interval = kRP2040IdleTicksPerUpdateInterval,
                                        .update_interval_ms = kRP2040CPUMonitorUpdateIntervalMs});
CPUMonitor core_1_monitor = CPUMonitor({.idle_ticks_per_update_interval = kRP2040IdleTicksPerUpdateInterval,
                                        .update_interval_ms = kRP2040CPUMonitorUpdateIntervalMs});

ADSBee adsbee = ADSBee({});
CommsManager comms_manager = CommsManager({});
ESP32SerialFlasher esp32_flasher = ESP32SerialFlasher({});

SettingsManager settings_manager;
ObjectDictionary object_dictionary;

// Define low-level coprocessor devices with overrides for things like GPIO and init functions.
ESP32 esp32_ll = ESP32({});

// Provide high-level coprocessor objects for interacting with coprocessor devices via low level class definitions.
SPICoprocessor esp32 = SPICoprocessor(
    {.interface = esp32_ll, .tag_str = "ESP32"});  // Use the low-level ESP32 interface to communicate with the ESP32.
ModeSPacketDecoder decoder = ModeSPacketDecoder({.enable_1090_error_correction = true});

int main() {
    bi_decl(bi_program_description("ADSBee 1090 ADSB Receiver"));

    // Initialize the temperature sensor.
    CPUMonitor::Init();

    // Initialize coprocessor SPI bus.
    // ESP32 SPI pins.
    gpio_set_function(bsp.copro_spi_clk_pin, GPIO_FUNC_SPI);
    gpio_set_function(bsp.copro_spi_mosi_pin, GPIO_FUNC_SPI);
    gpio_set_function(bsp.copro_spi_miso_pin, GPIO_FUNC_SPI);
    gpio_set_drive_strength(bsp.copro_spi_clk_pin, bsp.copro_spi_drive_strength);
    gpio_set_drive_strength(bsp.copro_spi_mosi_pin, bsp.copro_spi_drive_strength);
    gpio_set_pulls(bsp.copro_spi_clk_pin, bsp.copro_spi_pullup, bsp.copro_spi_pulldown);   // Clock pin pulls.
    gpio_set_pulls(bsp.copro_spi_mosi_pin, bsp.copro_spi_pullup, bsp.copro_spi_pulldown);  // MOSI pin pulls.
    gpio_set_pulls(bsp.copro_spi_miso_pin, bsp.copro_spi_pullup, bsp.copro_spi_pulldown);  // MISO pin pulls.
    // Initialize SPI Peripheral.
    spi_init(bsp.copro_spi_handle, bsp.copro_spi_clk_freq_hz);
    // The CC1312 straight up does not work with CPOL = 0 and CPHA = 0 (only sends one Byte per transaction then
    // explodes). The ESP32 doesn't seem to care either way (in fact it interprets CPOL = 1 CPHA = 1 as CPOL = 0 CPHA =
    // 0 just fine), so we stick with CPOL = 1 CPHA = 1.
    // I briefly tried switching the SPI format back and forth continuously in SPIBeginTransaction(), but this was
    // causing crashes.
    spi_set_format(bsp.copro_spi_handle,
                   8,           // Bits per transfer.
                   SPI_CPOL_1,  // Polarity (CPOL).
                   SPI_CPHA_1,  // Phase (CPHA).
                   SPI_MSB_FIRST);

    comms_manager.Init();
    comms_manager.console_printf("ADSBee 1090\r\nSoftware Version %d.%d.%d\r\n",
                                 object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                                 object_dictionary.kFirmwareVersionPatch);
    settings_manager.Load();  // Do this first so that we send the correct settings to the Sub-GHz radio on init.

    uint16_t num_status_led_blinks = FirmwareUpdateManager::AmWithinFlashPartition(0) ? 1 : 2;
    // Blink the LED a few times to indicate a successful startup.
    for (uint16_t i = 0; i < num_status_led_blinks; i++) {
        adsbee.SetStatusLED(true);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
        adsbee.SetStatusLED(false);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
    }

    adsbee.Init();
    adsbee.InitISRs();

    settings_manager.Apply();  // Run this before ESP32 firmware update attempt to ensure it's enabled properly.

    // If ESP32 is supported and enabled, try establishing communication with the ESP32 and maybe update its firmware.
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
#ifndef DEBUG_DISABLE_ESP32_FLASH
        // If we never read from the ESP32, or read a different firmware version, try writing to it.
        if (flash_esp32) {
            adsbee.DisableWatchdog();  // Disable watchdog while flashing.
            if (!esp32.DeInit()) {
                CONSOLE_ERROR("main", "Error while de-initializing ESP32 before flashing.");
            } else if (!esp32_flasher.FlashESP32()) {
                CONSOLE_ERROR("main", "Error while flashing ESP32. Disabling.");
                esp32.SetEnable(false);  // Disable ESP32 if flashing failed.
            } else if (!esp32.Init()) {
                CONSOLE_ERROR("main", "Error while re-initializing ESP32 after flashing.");
            }
            adsbee.EnableWatchdog();  // Restore watchdog after flashing.
        }
#endif
    }

    multicore_reset_core1();
    multicore_launch_core1(main_core1);

    uint32_t esp32_last_heartbeat_timestamp_ms = 0;

    while (true) {
        // Loop forever.
        core_0_monitor.Tick();
        core_0_monitor.Update();
        core_1_monitor.Update();

        decoder.UpdateLogLoop();
        comms_manager.Update();
        adsbee.Update();

        esp32.Update();

        // Poke the watchdog to keep things alive if the ESP32 is responding or if it's disabled.
        uint32_t old_esp32_last_heartbeat_timestamp_ms = esp32_last_heartbeat_timestamp_ms;
        esp32_last_heartbeat_timestamp_ms = esp32.GetLastHeartbeatTimestampMs();
        if (esp32_last_heartbeat_timestamp_ms != old_esp32_last_heartbeat_timestamp_ms || !esp32.IsEnabled()) {
            // Don't need to talk to the ESP32, or it acknowledged a heartbeat just now: poke the watchdog since nothing
            // seems amiss.
            adsbee.PokeWatchdog();
        }
    }
}