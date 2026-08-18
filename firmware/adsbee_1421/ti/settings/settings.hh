#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include <cstdint>
#include <functional>  // for strtoull

// #include "crc.hh"
#include "macros.hh"
#include "stdio.h"
#include "stdlib.h"  // for strtoull
#include "string.h"  // for memset
#ifdef ON_PICO
#include "pico/rand.h"
#endif

static constexpr uint32_t kSettingsVersion = 15;  // Change this when settings format changes!
static constexpr uint32_t kDeviceInfoVersion = 2;

class SettingsManager {
   public:
    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t { kConsole = 0, kNumSerialInterfaces };

    // Maximum number of sinks that can be passed to CommsManager::UpdateReporting() in a single call.
    // The 1421 has no IP feeds, so this is just the serial interface count. Per-protocol sink arrays in
    // the shared comms_reporting.cpp are sized with this.
    static constexpr uint16_t kMaxNumReportSinks = SerialInterface::kNumSerialInterfaces;
    static constexpr uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char kSerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum LogLevel : uint16_t { kSilent = 0, kErrors, kWarnings, kInfo, kNumLogLevels };
    static constexpr uint16_t kConsoleLogLevelStrMaxLen = 30;
    static const char kConsoleLogLevelStrs[LogLevel::kNumLogLevels][kConsoleLogLevelStrMaxLen];

    static const uint16_t kSubGHzModeStrMaxLen = 30;  // Length of Sub-GHz mode strings.

    // Reporting Protocol enum and string conversion array.
    enum ReportingProtocol : uint16_t {
        kNoReports = 0,
        kRaw,
        kBeast,
        kBeastNoUAT,
        kBeastNoUATUplink,
        kCSBee,
        kMAVLINK1,
        kMAVLINK2,
        kGDL90,
        kAircraftJSON,
        kGDL90NoUATUplink,  // Appended (not next to kGDL90): values are flash-persisted, don't renumber.
        kNumProtocols
    };
    static constexpr uint16_t kReportingProtocolStrMaxLen = 30;
    static const char kReportingProtocolStrs[ReportingProtocol::kNumProtocols][kReportingProtocolStrMaxLen];

    enum EnableState : int8_t {
        kEnableStateExternal = -1,  // Enable GPIO pin is high impedance.
        kEnableStateDisabled = 0,
        kEnableStateEnabled = 1
    };

    // Mode setting for the Sub-GHz radio (AT+SUBG_MODE). Values are flash-persisted: append new modes, don't
    // renumber. Future sub-GHz protocols (e.g. ADS-L, FLARM) get added here.
    enum SubGHzRadioMode : uint8_t {
        kSubGHzRadioModeUATRx = 0,      // UAT (978MHz): ADS-B + ground uplink reception.
        kSubGHzRadioModeUATRxNoUplink,  // UAT (978MHz): ADS-B only, uplink sync word disabled at the RF core.
        kNumSubGHzRadioModes
    };
    static const char kSubGHzModeStrs[kNumSubGHzRadioModes][kSubGHzModeStrMaxLen];

    // Sync mode for the 1090MHz Mode S receiver (how the LR2021 triggers reception).
    enum R1090PreambleMode : uint8_t {
        kR1090PreambleModeModeS = 0,  // Trigger on the standard Mode S preamble; hardware CRC filter on.
        kR1090PreambleModeDF17,       // Trigger on 2nd preamble half + DF17 header bits (better dynamic range).
        kR1090PreambleModeModeSSwCrc,  // Standard Mode S preamble with the hardware CRC off; software validates,
                                       // so failed-CRC frames stay available for error correction.
        kNumR1090PreambleModes
    };
    static constexpr uint16_t kR1090PreambleModeStrMaxLen = 30;
    static const char kR1090PreambleModeStrs[kNumR1090PreambleModes][kR1090PreambleModeStrMaxLen];

    // Receiver position settings.
    struct __attribute__((packed)) RxPosition {
        enum PositionSource : uint8_t {
            kPositionSourceNone = 0,
            kPositionSourceFixed = 1,
            kPositionSourceGNSS = 2,
            kPositionSourceLowestAircraft = 3,
            kPositionSourceAircraftMatchingICAO = 4,
            kNumPositionSources
        };

        static const uint16_t kPositionSourceStrMaxLen = 32;
        static const char kPositionSourceStrs[kNumPositionSources][kPositionSourceStrMaxLen];

        PositionSource source = kPositionSourceLowestAircraft;
        float latitude_deg = 0.0;      // Degrees, WGS84
        float longitude_deg = 0.0;     // Degrees, WGS84
        int32_t gnss_altitude_ft = 0;  // Meters, WGS84
        int32_t baro_altitude_ft = 0;  // Meters, AMSL
        float heading_deg = 0.0;       // Degrees from true north
        int32_t speed_kts = 0;         // Speed over ground in knots
        uint32_t icao_address =
            0;  // ICAO address to use for position bootstrap when source is kPositionSourceICAO, or the ICAO of the
                // lowest plane being tracked when source is kPositionSourceLowestAircraft.
    };

    // This struct contains nonvolatile settings that should persist across reboots but may be overwritten during a
    // firmware upgrade if the format of the settings struct changes.
    struct alignas(4) Settings {
        static constexpr uint32_t kDefaultWatchdogTimeoutSec = 10;
        // NOTE: Lengths do not include null terminator.
        // Single source of truth for the console boot baud rate: CommsManagerConfig defaults to this,
        // and Apply() falls back to it if the stored rate isn't whitelisted.
        static constexpr uint32_t kDefaultUARTBaudRate = 1000000;

        // Network-related string length constants. The 1421 has no network interfaces, but
        // common/coprocessor/object_dictionary.hh (pulled in via spi_coprocessor_packet.hh from
        // composite_array.cpp) sizes its ESP32NetworkInfo wire struct with these, so they must
        // exist here (this file shadows common/settings/settings.hh) and match the values in
        // common/settings/settings.hh to keep the wire layout identical.
        static constexpr uint16_t kWiFiSSIDMaxLen = 31;
        static constexpr uint16_t kWiFiMaxNumClients = 6;
        static constexpr uint16_t kIPAddrStrLen = 16;   // XXX.XXX.XXX.XXX (does not include null terminator)
        static constexpr uint16_t kMACAddrStrLen = 18;  // XX:XX:XX:XX:XX:XX (does not include null terminator)
        static constexpr uint16_t kMACAddrNumBytes = 6;

        // Actual settings values start here.
        uint32_t settings_version = kSettingsVersion;

        // ADSBee settings
        bool r1090_rx_enabled = true;
        uint32_t watchdog_timeout_sec = kDefaultWatchdogTimeoutSec;
        R1090PreambleMode r1090_preamble_mode = R1090PreambleMode::kR1090PreambleModeDF17;
        uint8_t r1090_gain = 0;      // 0 = auto AGC, 1..15 manual (13 = max). Default: auto.
        uint8_t r1090_rx_boost = 0;  // LF RX path boost, 0 (off) .. 7 (max).

        // CommunicationsManager settings
        LogLevel log_level = LogLevel::kWarnings;
        ReportingProtocol reporting_protocols[SerialInterface::kNumSerialInterfaces] = {
            ReportingProtocol::kNoReports,  // Console
        };
        uint32_t baud_rates[SerialInterface::kNumSerialInterfaces] = {
            kDefaultUARTBaudRate,  // Console
        };

        // Sub-GHz settings
        bool subg_rx_enabled = true;
        SubGHzRadioMode subg_mode = SubGHzRadioMode::kSubGHzRadioModeUATRx;  // Default to UAT mode (978MHz receiver).

        // MAVLINK settings
        uint8_t mavlink_system_id = 1;
        uint8_t mavlink_component_id = 156;  // Default to MAV_COMP_ID_ADSB (156).

        // Receiver position settings
        RxPosition rx_position;

        /**
         * Default constructor.
         */
        Settings() {}
    };

    // This struct contains device information that should persist across firmware upgrades.
    struct DeviceInfo {
        // NOTE: Lengths do not include null terminator.
        static constexpr uint16_t kPartCodeLen = 26;  // NNNNNNNNNR-YYYYMMDD-VVXXXX (not counting end of string char).
        static constexpr uint16_t kPartCodePartNumberLen = 9;  // Not counting rev letter or end of string char.
        static constexpr uint16_t kOTAKeyMaxLen = 128;
        static constexpr uint16_t kNumOTAKeys = 2;

        uint32_t device_info_version = kDeviceInfoVersion;
        char part_code[kPartCodeLen + 1];
        char ota_keys[kNumOTAKeys][kOTAKeyMaxLen + 1];

        enum ADSBeePartNumber : uint32_t {
            // WARNING: These can't have a leading 0, or they will be encoded as octal and not decimal!
            kPNADSBee1090 = 10240002,                  // ADSBee 1090
            kPNADSBee1090U = 10250002,                 // ADSBee 1090U
            kPNADSBee1090UIndoorPoEFeeder = 40250002,  // ADSBee 1090U Indoor PoE Feeder
            kPNADSBeem1090 = 10250007,                 // ADSBee m1090
            kPNADSBeem1090EvalBoard = 10250013,        // ADSBee m1090 Eval Board
            kPNGS3MPoE = 40250001                      // GS3M PoE
        };

        /**
         * Default constructor.
         */
        DeviceInfo() { memset(part_code, '\0', kPartCodeLen + 1); }

        /**
         * Extracts the part number and revision from the part code.
         * @retval Part number as an integer.
         */
        uint32_t GetPartNumber() {
            char part_number_buf[kPartCodePartNumberLen + 1] = {0};
            memcpy(part_number_buf, part_code, kPartCodePartNumberLen);
            return strtoul(
                part_number_buf, nullptr,
                10);  // Convert part number to integer (read part code string as base 10, without the rev letter).
        }

        /**
         * Extracts the part revision character from the part code.
         * @retval Character representing the part revision.
         */
        char GetPartRev() { return part_code[kPartCodePartNumberLen]; }
    };

    /**
     * Applies internal settings to the relevant objects. This is only used after the settings struct has been
     * updated by loading it from EEPROM or by overwriting it via the coprocessor SPI bus.
     */
    bool Apply();

    /**
     * Helper function for reconstructing an AT command value for a given EnableState.
     * @param[in] state EnableState to convert to a string.
     * @retval String representation of the EnableState, as it would be used in an AT command.
     */
    static inline const char* EnableStateToATValueStr(EnableState state) {
        switch (state) {
            case kEnableStateExternal:
                return "EXTERNAL";
            case kEnableStateEnabled:
                return "1";
            case kEnableStateDisabled:
                return "0";
            default:
                return "?";
        }
    }

    /**
     * Used to retrieve device information, either directly from EEPROM or via interprocessor SPI bus.
     * @param[in] device_info DeviceInfo struct to set.
     * @retval True if device info was retrieved successfully, false otherwise.
     */
    static bool GetDeviceInfo(DeviceInfo& device_info);

    /**
     * Used to set device information, which is stored in flash and should persist across firmware updates.
     * @param[in] device_info DeviceInfo struct to set.
     * @retval True if device info was set successfully, false otherwise.
     */
    static bool SetDeviceInfo(const DeviceInfo& device_info);

    /**
     * Loads settings from EEPROM. Assumes settings are stored at address 0x0 and doesn't do any integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Load();

    /**
     * Print the settings in human-readable format.
     */
    void Print();

    /**
     * Print the settings in AT command format. Used for dumping settings before a firmware update.
     */
    void PrintAT();

    /**
     * Takes a password as a string and fills a buffer with the corresponding number of asterix.
     * @param[in] password_buf Buffer to read the password from. Must be at least password_len+1 chars.
     * @param[out] redacted_password_buf Buffer to write the asterix to. Must be at least password_len+1 chars.
     * @param[in] buf_len Maximum allowable number of characteers in the password. Used to guard against falling off
     * the end of the string. Not used for actually finding ther number of asterix to print.
     */
    static inline void RedactPassword(char* password_buf, char* redacted_password_buf, uint16_t buf_len) {
        uint16_t password_len = MIN(strnlen(password_buf, buf_len), buf_len);
        memset(redacted_password_buf, '*', password_len);
        redacted_password_buf[password_len] = '\0';
    }

    /**
     * Saves settings to EEPROM. Stores settings at address 0x0 and performs no integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Save();

    /**
     * Restores settings to factory default values.
     */
    void ResetToDefaults();

    Settings settings;

   private:
};

extern SettingsManager settings_manager;

#endif /* SETTINGS_HH_ */