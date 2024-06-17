#ifndef COMMS_HH_
#define COMMS_HH_

#include "cpp_at.hh"
#include "hardware/uart.h"

class CommsManager {
   public:
    static const uint16_t kATCommandBufMaxLen = 1000;
    static const uint32_t kDefaultCommsUARTBaudrate = 115200;
    static const uint32_t kDefaultGNSSUARTBaudrate = 9600;
    static const uint16_t kPrintfBufferMaxSize = 500;

    // NOTE: Length does not include null terminator.
    static const uint16_t kWiFiSSIDMaxLen = 32;
    static const uint16_t kWiFiPasswordMaxLen = 32;  // Theoretical max is 63, but limited by CppAT arg max len.

    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t { kConsole = 0, kCommsUART, kGNSSUART, kNumSerialInterfaces };
    static const uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char SerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum ConsoleVerbosity : uint16_t { kSilent = 0, kErrors, kWarnings, kLogs, kNumVerbosityLevels };
    static const uint16_t kConsoleVerbosityStrMaxLen = 30;
    static const char ConsoleVerbosityStrs[ConsoleVerbosity::kNumVerbosityLevels][kConsoleVerbosityStrMaxLen];

    // Reporting Protocol enum and string conversion array.
    enum ReportingProtocol : uint16_t {
        kNoReports = 0,
        kRaw,
        kRawValidated,
        kMAVLINK1,
        kMAVLINK2,
        kGDL90,
        kNumProtocols
    };
    static const uint16_t kReportingProtocolStrMaxLen = 30;
    static const char ReportingProtocolStrs[ReportingProtocol::kNumProtocols][kReportingProtocolStrMaxLen];

    struct CommsManagerConfig {
        uart_inst_t *comms_uart_handle = uart1;
        uint16_t comms_uart_tx_pin = 4;
        uint16_t comms_uart_rx_pin = 5;
        uart_inst_t *gnss_uart_handle = uart0;
        uint16_t gnss_uart_tx_pin = 0;
        uint16_t gnss_uart_rx_pin = 1;
        uint16_t uart_timeout_us = 0;  // Time to wait for a character if there isn't one alredy available.

        uint16_t esp32_enable_pin = 14;
        uint16_t esp32_gpio0_boot_pin = 11;
    };

    CommsManager(CommsManagerConfig config_in);
    bool Init();
    bool Update();

    CPP_AT_CALLBACK(ATBaudrateCallback);
    CPP_AT_CALLBACK(ATConsoleVerbosityCallback);
    CPP_AT_CALLBACK(ATProtocolCallback);
    CPP_AT_HELP_CALLBACK(ATProtocolHelpCallback);
    CPP_AT_CALLBACK(ATRxGainCallback);
    CPP_AT_CALLBACK(ATSettingsCallback);
    CPP_AT_CALLBACK(ATTLReadCallback);
    CPP_AT_CALLBACK(ATTLSetCallback);
    CPP_AT_CALLBACK(ATWiFiCallback);

    int console_printf(const char *format, ...);
    int console_level_printf(ConsoleVerbosity level, const char *format, ...);
    int iface_printf(SerialInterface iface, const char *format, ...);
    bool iface_putc(SerialInterface iface, char c);
    bool iface_getc(SerialInterface iface, char &c);
    bool iface_puts(SerialInterface iface, const char *buf);

    /**
     * Sets the baudrate for a serial interface.
     * @param[in] iface SerialInterface to set baudrate for.
     * @param[in] baudrate Baudrate to set.
     * @retval True if the baudrate could be set, false if the interface specified does not support a baudrate.
     */
    bool SetBaudrate(SerialInterface iface, uint32_t baudrate) {
        switch (iface) {
            case kCommsUART:
                // Save the actual set value as comms_uart_baudrate_.
                comms_uart_baudrate_ = uart_set_baudrate(config_.comms_uart_handle, baudrate);
                return true;
                break;
            case kGNSSUART:
                // Save the actual set value as gnss_uart_baudrate_.
                gnss_uart_baudrate_ = uart_set_baudrate(config_.gnss_uart_handle, baudrate);
                return true;
                break;
            default:
                return false;  // Other interfaces don't have a baudrate.
        }
        return false;  // Should never get here.
    }

    /**
     * Returns the currently set baudrate for a serial interface.
     * @param[in] iface SerialInterface to get the baudrate for.
     * @param[out] baudrate Reference to uint32_t to fill with retrieved value.
     * @retval True if baudrate retrieval succeeded, false if iface does not support a baudrate.
     */
    bool GetBaudrate(SerialInterface iface, uint32_t &baudrate) {
        switch (iface) {
            case kCommsUART:
                // Save the actual set value as comms_uart_baudrate_.
                baudrate = comms_uart_baudrate_;
                return true;
                break;
            case kGNSSUART:
                // Save the actual set value as gnss_uart_baudrate_.
                baudrate = gnss_uart_baudrate_;
                return true;
                break;
            default:
                return false;  // Other interfaces don't have a baudrate.
        }
        return false;  // Should never get here.
    }

    /**
     * Specify the reporting protocol for a given serial interface.
     * @param[in] iface SerialInterface to set reporting protocol on.
     * @param[in] protocol Reporting protocol to set on iface.
     * @retval True if succeeded, false otherwise.
     */
    bool SetReportingProtocol(SerialInterface iface, ReportingProtocol protocol) {
        reporting_protocols_[iface] = protocol;
        return true;
    }

    /**
     * Get the reporting protocol for a given serial interface.
     * @param[in] iface SerialInterface to get the reporting protocol from.
     * @param[out] protocol reference to ReportingProtocol to fill with result.
     * @retval True if reportig protocol could be retrieved, false otherwise.
     */
    bool GetReportingProtocol(SerialInterface iface, ReportingProtocol &protocol) {
        protocol = reporting_protocols_[iface];
        return true;
    }

    /**
     * Returns whether WiFi is enabled.
     * @retval True if WiFi is enabled, false otherwise.
     */
    bool WiFiIsEnabled() { return wifi_enabled_; }

    bool SetWiFiEnabled(bool new_wifi_enabled);

    // Public console settings.
    ConsoleVerbosity console_verbosity = ConsoleVerbosity::kLogs;  // Start with highest verbosity by default.
    uint32_t last_report_timestamp_ms = 0;

    // Public WiFi Settings
    char wifi_ssid[kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_password[kWiFiPasswordMaxLen + 1];  // Add space for null terminator.

    // MAVLINK settings.
    uint32_t mavlink_reporting_interval_ms = 1000;
    uint8_t mavlink_system_id = 0;
    uint8_t mavlink_component_id = 0;

   private:
    // AT Functions
    bool InitAT();
    bool UpdateAT();

    // Reporting Functions
    bool InitReporting();
    bool UpdateReporting();

    /**
     * Sends a series of MAVLINK ADSB_VEHICLE messages on the selected serial interface, one for each tracked aircraft
     * in the aircraft dictionary, plus a MAVLINK MESSAGE_INTERVAL message used as a delimiter at the end of the train
     * of ADSB_VEHICLE messages.
     * @param[in] iface SerialInterface to broadcast MAVLINK messages on. Note that this gets cast to a MAVLINK channel
     * as a bit of a dirty hack under the hood, then un-cast back into a SerialInterface in the UART send function
     * within MAVLINK. Shhhhhhh it's fine for now.
     * @retval True if successful, false if something went sideways.
     */
    bool ReportMAVLINK(SerialInterface iface);

    CommsManagerConfig config_;

    // Console Settings
    CppAT at_parser_;

    // Reporting Settings
    uint32_t comms_uart_baudrate_ = kDefaultCommsUARTBaudrate;
    uint32_t gnss_uart_baudrate_ = kDefaultGNSSUARTBaudrate;
    ReportingProtocol reporting_protocols_[SerialInterface::kNumSerialInterfaces - 1] = {
        ReportingProtocol::kNoReports, ReportingProtocol::kMAVLINK1};  // GNSS_UART not included.

    // private WiFi Settings
    bool wifi_enabled_ = false;
};

extern CommsManager comms_manager;

#define TEXT_COLOR_RED              "\033[31m"
#define TEXT_COLOR_GREEN            "\033[32m"
#define TEXT_COLOR_YELLOW           "\033[33m" /* orange on some systems */
#define TEXT_COLOR_BLUE             "\033[34m"
#define TEXT_COLOR_MAGENTA          "\033[35m"
#define TEXT_COLOR_CYAN             "\033[36m"
#define TEXT_COLOR_LIGHT_GRAY       "\033[37m"
#define TEXT_COLOR_DARK_GRAY        "\033[90m"
#define TEXT_COLOR_BRIGHT_RED       "\033[91m"
#define TEXT_COLOR_BRIGHT_GREEN     "\033[92m"
#define TEXT_COLOR_BRIGHT_YELLOW    "\033[93m"
#define TEXT_COLOR_BRIGHT_BLUE      "\033[94m"
#define TEXT_COLOR_BRIGHT_MAGENTA   "\033[95m"
#define TEXT_COLOR_BRIGHT_CYAN      "\033[96m"
#define TEXT_COLOR_WHITE            "\033[97m"

#define TEXT_COLOR_RESET            "\033[0m"

#define CONSOLE_PRINTF(format, ...) comms_manager.console_printf(format __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_LOG(format, ...) \
    comms_manager.console_level_printf(CommsManager::ConsoleVerbosity::kLogs, format "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_WARNING(format, ...)                                              \
    comms_manager.console_level_printf(CommsManager::ConsoleVerbosity::kWarnings, \
                                       TEXT_COLOR_YELLOW format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_ERROR(format, ...)                                              \
    comms_manager.console_level_printf(CommsManager::ConsoleVerbosity::kErrors, \
                                       TEXT_COLOR_RED format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */