#include "settings.hh"

#include "adsbee.hh"
#include "comms.hh"
#include "flash_utils.hh"
#include "sub_ghz_radio.hh"

/* CC1314R10 (CC13X4) flash: 1 MB (0x00000000 - 0x000FFFFF)
   Flash sector size: 2 KB (0x800), region size: 8 KB (4 sectors)
   FLASH MAP
       0x00000000  (~1008k)  FLASH_APP           Application Code and Data
       0x000FC000  (8k)      FLASH_SETTINGS      Settings   (4 x 2KB sectors)
       0x000FE000  (8k)      FLASH_DEVICE_INFO   Device Info (4 x 2KB sectors)
*/
static const uint32_t kFlashSettingsStartAddr = 0x000FC000;
static const uint32_t kFlashDeviceInfoStartAddr =
    0x000FE000;  // = kFlashSettingsStartAddr + kFlashSettingsRegionSizeBytes

static_assert(sizeof(SettingsManager::Settings) < FlashUtils::kFlashSettingsRegionSizeBytes);
static_assert(sizeof(SettingsManager::DeviceInfo) < FlashUtils::kFlashSettingsRegionSizeBytes);
// Make sure settings struct doesn't run into device info.
static_assert(sizeof(SettingsManager::Settings) < kFlashDeviceInfoStartAddr - kFlashSettingsStartAddr);

bool SettingsManager::Apply() {
    bool success = true;

    // All of these can fail if the radio fails to open/close or the RX command can't be restarted; fold that
    // into the return value so boot/LOAD callers can see it.
    // LR2021 interface enable must be applied first: with lr2021_enabled = false, the receiver-config
    // calls below must never drive the (released) bus, which the ApplyReceiverConfigInner() gate
    // guarantees only once the flag is set.
    success &= adsbee.SetLR2021Enabled(settings.lr2021_enabled);
    success &= adsbee.SetRx1090Enabled(settings.r1090_rx_enabled);
    success &= adsbee.SetRxSubGHzEnabled(settings.subg_rx_enabled);
    // subg_radio.Init() runs before Apply() at boot (see main.cpp), so a persisted non-default mode costs one RX
    // restart here; SetMode() is a no-op when the mode is unchanged.
    success &= subg_radio.SetMode(settings.subg_mode);
    adsbee.SetWatchdogTimeoutSec(settings.watchdog_timeout_sec);
    adsbee.SetR1090PreambleMode(settings.r1090_preamble_mode);
    adsbee.SetR1090Gain(settings.r1090_gain);
    adsbee.SetR1090RxBoost(settings.r1090_rx_boost);
    adsbee.rx_position = settings.rx_position;

    // Apply reporting protocols.
    // comms_manager.SetReportingProtocol(SerialInterface::kCommsUART,
    //                                    settings.reporting_protocols[SerialInterface::kCommsUART]);
    comms_manager.SetReportingProtocol(SerialInterface::kConsole,
                                       settings.reporting_protocols[SerialInterface::kConsole]);

    // Apply the stored console baud rate (persisted via AT+SETTINGS=SAVE). Guard against corrupt
    // flash by falling back to the default. No-op when the rate already matches — the common case at
    // boot, since the UART opens at the default rate.
    uint32_t baud = settings.baud_rates[SerialInterface::kConsole];
    if (!CommsManager::IsAllowedBaudRate(baud)) {
        baud = Settings::kDefaultUARTBaudRate;
        settings.baud_rates[SerialInterface::kConsole] = baud;
    }
    success &= comms_manager.SetBaudRate(baud);

    // All other parameters are stored directly in the global setting struct and don't need to be applied.

    return success;  // Not currently doing any error checking here, relying on AT commands to limit parameters to
                     // allowable ranges. Could be a problem if loading from corrupted EEPROM.
}

bool SettingsManager::GetDeviceInfo(DeviceInfo& device_info) {
    // Device Info is stored in flash.
    device_info = *(DeviceInfo*)(kFlashDeviceInfoStartAddr);
    return true;
}

bool SettingsManager::Load() {
    // Load settings from flash.
    memcpy(&settings, (const void*)kFlashSettingsStartAddr, sizeof(Settings));

    // Reset to defaults if loading from a blank flash.
    if (settings.settings_version != kSettingsVersion) {
        CONSOLE_ERROR("settingsManager::Settings::Load",
                      "Settings version mismatch. Expected %d, got %d. Resetting to defaults.", kSettingsVersion,
                      settings.settings_version);

        ResetToDefaults();  // Reset to defaults with part number specific overrides.

        FlashUtils::FlashSafe();
        FlashUtils::EraseRegion(kFlashSettingsStartAddr);
        FlashUtils::Program(kFlashSettingsStartAddr, (uint8_t*)&settings, sizeof(settings));
        FlashUtils::FlashUnsafe();
    }

    return true;
}

bool SettingsManager::Save() {
    // Save reporting protocols.
    comms_manager.GetReportingProtocol(SerialInterface::kConsole,
                                       settings.reporting_protocols[SerialInterface::kConsole]);

    // Sync live runtime values into the settings struct before flashing. These are owned by the
    // adsbee object (their AT set-commands only update adsbee), so without this they would persist
    // stale. This mirrors the reverse copy performed in Apply().
    settings.lr2021_enabled = adsbee.LR2021IsEnabled();
    settings.r1090_rx_enabled = adsbee.Rx1090IsEnabled();
    settings.subg_rx_enabled = adsbee.RxSubGHzIsEnabled();
    settings.subg_mode = subg_radio.GetMode();
    settings.watchdog_timeout_sec = adsbee.GetWatchdogTimeoutSec();
    settings.r1090_preamble_mode = adsbee.GetR1090PreambleMode();
    settings.r1090_gain = adsbee.GetR1090Gain();
    settings.r1090_rx_boost = adsbee.GetR1090RxBoost();
    settings.rx_position = adsbee.rx_position;
    // Live console baud — AT+BAUD_RATE only changes the running rate; SAVE is what persists it.
    settings.baud_rates[SerialInterface::kConsole] = comms_manager.GetBaudRate();

    FlashUtils::FlashSafe();
    FlashUtils::EraseRegion(kFlashSettingsStartAddr);
    FlashUtils::Program(kFlashSettingsStartAddr, (uint8_t*)&settings, sizeof(settings));
    FlashUtils::FlashUnsafe();
    return true;
}

void SettingsManager::ResetToDefaults() {
    Settings default_settings;
    settings = default_settings;

    // Override default settings with board-specific defaults.
    // NOTE: This section is not currently used.
    DeviceInfo device_info;
    if (GetDeviceInfo(device_info)) {
        switch (device_info.GetPartNumber()) {
            case DeviceInfo::kPNADSBee1090:
            case DeviceInfo::kPNGS3MPoE:  // Nothing special needed for GS3M PoE since it's all taken care of by core
                                          // network settings.
            case DeviceInfo::kPNADSBee1090U:
            case DeviceInfo::kPNADSBeem1090:
            case DeviceInfo::kPNADSBeem1090EvalBoard:
            default:
                // No changes needed, these use the default settings.
                break;
        }
    }
}

bool SettingsManager::SetDeviceInfo(const DeviceInfo& device_info) {
    // Device Info is stored in flash.
    FlashUtils::FlashSafe();
    FlashUtils::EraseRegion(kFlashDeviceInfoStartAddr);
    FlashUtils::Program(kFlashDeviceInfoStartAddr, (uint8_t*)&device_info, sizeof(device_info));
    FlashUtils::FlashUnsafe();
    return true;
}

// NOTE: This function needs to be updated separately for ESP32.
// Each field is read from the same source its own AT+<X>? query uses, so AT+SETTINGS? agrees with
// the individual queries. Printed line-by-line (rather than into one fixed buffer) since the full
// output is too large for a single stack buffer.
void SettingsManager::Print() {
    CONSOLE_PRINTF("Settings Struct (version %lu)\r\n", settings.settings_version);

    // ADSBee settings
    CONSOLE_PRINTF("\tLR2021 Interface: %s\r\n", adsbee.LR2021IsEnabled() ? "ENABLED" : "DISABLED (bus released)");
    CONSOLE_PRINTF("\t1090 Receiver: %s\r\n", adsbee.Rx1090IsEnabled() ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF("\tSub-GHz Receiver: %s\r\n", adsbee.RxSubGHzIsEnabled() ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF("\tSub-GHz Mode: %s\r\n", kSubGHzModeStrs[subg_radio.GetMode()]);
    CONSOLE_PRINTF("\tWatchdog Timeout: %lu seconds\r\n", adsbee.GetWatchdogTimeoutSec());
    CONSOLE_PRINTF("\t1090 Preamble Mode: %s\r\n", kR1090PreambleModeStrs[adsbee.GetR1090PreambleMode()]);
    CONSOLE_PRINTF("\t1090 Gain: %u (0 = auto AGC)\r\n", adsbee.GetR1090Gain());
    CONSOLE_PRINTF("\t1090 RX Boost: %u (0 = off, 7 = max)\r\n", adsbee.GetR1090RxBoost());

    // CommunicationsManager settings
    CONSOLE_PRINTF("\tLog Level: %s\r\n", kConsoleLogLevelStrs[settings.log_level]);
    for (uint16_t i = 0; i < SerialInterface::kNumSerialInterfaces; i++) {
        CONSOLE_PRINTF("\tReporting Protocol [%s]: %s\r\n", kSerialInterfaceStrs[i],
                       kReportingProtocolStrs[settings.reporting_protocols[i]]);
    }
    for (uint16_t i = 0; i < SerialInterface::kNumSerialInterfaces; i++) {
        CONSOLE_PRINTF("\tBaud Rate [%s]: %lu\r\n", kSerialInterfaceStrs[i], settings.baud_rates[i]);
    }

    // MAVLINK settings
    CONSOLE_PRINTF("\tMAVLink System ID: %u\r\n", settings.mavlink_system_id);
    CONSOLE_PRINTF("\tMAVLink Component ID: %u\r\n", settings.mavlink_component_id);

    // Receiver position settings (live values, mirroring the AT+RX_POSITION? query).
    CONSOLE_PRINTF("\tReceiver Position:\r\n");
    CONSOLE_PRINTF("\t\tSource: %s [%s]\r\n", RxPosition::kPositionSourceStrs[adsbee.rx_position.source],
                   adsbee.rx_position_available ? "OK" : "NOT AVAILABLE");
    CONSOLE_PRINTF("\t\tLatitude: %.6f deg\r\n", adsbee.rx_position.latitude_deg);
    CONSOLE_PRINTF("\t\tLongitude: %.6f deg\r\n", adsbee.rx_position.longitude_deg);
    CONSOLE_PRINTF("\t\tGNSS Altitude: %d ft\r\n", adsbee.rx_position.gnss_altitude_ft);
    CONSOLE_PRINTF("\t\tBarometric Altitude: %d ft\r\n", adsbee.rx_position.baro_altitude_ft);
    CONSOLE_PRINTF("\t\tHeading: %.1f deg\r\n", adsbee.rx_position.heading_deg);
    CONSOLE_PRINTF("\t\tSpeed: %d kts\r\n", adsbee.rx_position.speed_kts);
    CONSOLE_PRINTF("\t\tICAO: 0x%06X\r\n", adsbee.rx_position.icao_address);
}

// Emits a complete, re-applicable set of AT commands. Live values are read from the same sources
// as each command's AT+<X>? query so that the dump reflects (and round-trips) the running config.
void SettingsManager::PrintAT() {
    // AT+BAUD_RATE: deliberately not dumped. Replaying it mid-restore would switch the console baud
    // out from under the host. The baud persists via the settings struct itself; after a settings
    // wipe the device boots at the default rate.

    // AT+DEVICE_INFO: Don't store this.

    // AT+LOG_LEVEL
    CONSOLE_PRINTF("AT+LOG_LEVEL=%s\r\n", kConsoleLogLevelStrs[settings.log_level]);

    // AT+LR_ENABLE: must precede the R1090_*/RX_ENABLE commands so replaying a dump onto a
    // bus-released device re-drives the LR2021 pins before any command that reconfigures the chip
    // (with =0 first, the later R1090 commands just update mirrors and defer harmlessly).
    CONSOLE_PRINTF("AT+LR_ENABLE=%d\r\n", adsbee.LR2021IsEnabled());

    // AT+MAVLINK_ID
    CONSOLE_PRINTF("AT+MAVLINK_ID=%u,%u\r\n", settings.mavlink_system_id, settings.mavlink_component_id);

    // AT+PROTOCOL_OUT
    for (uint16_t i = 0; i < SerialInterface::kNumSerialInterfaces; i++) {
        CONSOLE_PRINTF("AT+PROTOCOL_OUT=%s,%s\r\n", kSerialInterfaceStrs[i],
                       kReportingProtocolStrs[settings.reporting_protocols[i]]);
    }

    // AT+R1090_GAIN
    CONSOLE_PRINTF("AT+R1090_GAIN=%u\r\n", adsbee.GetR1090Gain());

    // AT+R1090_RX_BOOST
    CONSOLE_PRINTF("AT+R1090_RX_BOOST=%u\r\n", adsbee.GetR1090RxBoost());

    // AT+R1090_PREAMBLE
    CONSOLE_PRINTF("AT+R1090_PREAMBLE=%s\r\n", kR1090PreambleModeStrs[adsbee.GetR1090PreambleMode()]);

    // AT+RX_ENABLE: leading arg left empty so the "all enabled" override is skipped and the 1090
    // and Sub-GHz receivers are restored independently.
    CONSOLE_PRINTF("AT+RX_ENABLE=,%d,%d\r\n", adsbee.Rx1090IsEnabled(), adsbee.RxSubGHzIsEnabled());

    // AT+RX_POSITION: reconstruct only the args the selected source accepts.
    switch (adsbee.rx_position.source) {
        case RxPosition::PositionSource::kPositionSourceFixed:
            CONSOLE_PRINTF("AT+RX_POSITION=%s,%.6f,%.6f,%d,%d,%.1f,%d\r\n",
                           RxPosition::kPositionSourceStrs[adsbee.rx_position.source],
                           adsbee.rx_position.latitude_deg, adsbee.rx_position.longitude_deg,
                           adsbee.rx_position.gnss_altitude_ft, adsbee.rx_position.baro_altitude_ft,
                           adsbee.rx_position.heading_deg, adsbee.rx_position.speed_kts);
            break;
        case RxPosition::PositionSource::kPositionSourceAircraftMatchingICAO:
            CONSOLE_PRINTF("AT+RX_POSITION=%s,%06X\r\n",
                           RxPosition::kPositionSourceStrs[adsbee.rx_position.source],
                           adsbee.rx_position.icao_address);
            break;
        default:
            CONSOLE_PRINTF("AT+RX_POSITION=%s\r\n", RxPosition::kPositionSourceStrs[adsbee.rx_position.source]);
            break;
    }

    // AT+SUBG_MODE
    CONSOLE_PRINTF("AT+SUBG_MODE=%s\r\n", kSubGHzModeStrs[subg_radio.GetMode()]);

    // AT+WATCHDOG
    CONSOLE_PRINTF("AT+WATCHDOG=%lu\r\n", adsbee.GetWatchdogTimeoutSec());
}
