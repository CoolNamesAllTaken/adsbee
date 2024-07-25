#ifndef COMMS_HH_
#define COMMS_HH_

// #include "transponder_packet.hh"  // For DecodedTransponderPacket.
#include "ads_bee.hh"
#include "cpp_at.hh"
#include "data_structures.hh"  // For PFBQueue.
#include "hardware/uart.h"
#include "settings.hh"

class CommsManager {
   public:
    static const uint16_t kATCommandBufMaxLen = 1000;
    static const uint16_t kPrintfBufferMaxSize = 500;

    struct CommsManagerConfig {
        uart_inst_t *comms_uart_handle = uart1;
        uint16_t comms_uart_tx_pin = 4;
        uint16_t comms_uart_rx_pin = 5;
        uart_inst_t *gnss_uart_handle = uart0;
        uint16_t gnss_uart_tx_pin = 0;
        uint16_t gnss_uart_rx_pin = 1;
        uint16_t uart_timeout_us = 0;  // Time to wait for a character if there isn't one alredy available.

        uint16_t esp32_enable_pin = 14;
        uint16_t esp32_gpio0_boot_pin = 13;
        uint16_t esp32_mosi_pin = 8;
        uint16_t esp32_miso_pin = 9;
        uint16_t esp32_clk_pin = 7;
        uint16_t esp32_cs_pin = 10;
    };

    CommsManager(CommsManagerConfig config_in);
    bool Init();
    bool Update();

    CPP_AT_CALLBACK(ATBaudrateCallback);
    CPP_AT_CALLBACK(ATLogLevelCallback);
    CPP_AT_CALLBACK(ATFlashESP32Callback);
    CPP_AT_CALLBACK(ATProtocolCallback);
    CPP_AT_HELP_CALLBACK(ATProtocolHelpCallback);
    CPP_AT_CALLBACK(ATRxEnableCallback);
    CPP_AT_CALLBACK(ATRxGainCallback);
    CPP_AT_CALLBACK(ATSettingsCallback);
    CPP_AT_CALLBACK(ATTLReadCallback);
    CPP_AT_CALLBACK(ATTLSetCallback);
    CPP_AT_CALLBACK(ATWiFiCallback);

    int console_printf(const char *format, ...);
    int console_level_printf(SettingsManager::LogLevel level, const char *format, ...);
    int iface_printf(SettingsManager::SerialInterface iface, const char *format, ...);
    bool iface_putc(SettingsManager::SerialInterface iface, char c);
    bool iface_getc(SettingsManager::SerialInterface iface, char &c);
    bool iface_puts(SettingsManager::SerialInterface iface, const char *buf);

    /**
     * Sets the baudrate for a serial interface.
     * @param[in] iface SerialInterface to set baudrate for.
     * @param[in] baudrate Baudrate to set.
     * @retval True if the baudrate could be set, false if the interface specified does not support a baudrate.
     */
    bool SetBaudrate(SettingsManager::SerialInterface iface, uint32_t baudrate) {
        switch (iface) {
            case SettingsManager::kCommsUART:
                // Save the actual set value as comms_uart_baudrate_.
                comms_uart_baudrate_ = uart_set_baudrate(config_.comms_uart_handle, baudrate);
                return true;
                break;
            case SettingsManager::kGNSSUART:
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
    bool GetBaudrate(SettingsManager::SerialInterface iface, uint32_t &baudrate) {
        switch (iface) {
            case SettingsManager::kCommsUART:
                // Save the actual set value as comms_uart_baudrate_.
                baudrate = comms_uart_baudrate_;
                return true;
                break;
            case SettingsManager::kGNSSUART:
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
    bool SetReportingProtocol(SettingsManager::SerialInterface iface, SettingsManager::ReportingProtocol protocol) {
        reporting_protocols_[iface] = protocol;
        return true;
    }

    /**
     * Get the reporting protocol for a given serial interface.
     * @param[in] iface SerialInterface to get the reporting protocol from.
     * @param[out] protocol reference to ReportingProtocol to fill with result.
     * @retval True if reportig protocol could be retrieved, false otherwise.
     */
    bool GetReportingProtocol(SettingsManager::SerialInterface iface, SettingsManager::ReportingProtocol &protocol) {
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
    SettingsManager::LogLevel log_level = SettingsManager::LogLevel::kInfo;  // Start with highest verbosity by default.
    uint32_t last_report_timestamp_ms = 0;

    // Queue for storing transponder packets before they get reported.
    PFBQueue<DecodedTransponderPacket> transponder_packet_reporting_queue =
        PFBQueue<DecodedTransponderPacket>({.buf_len_num_elements = ADSBee::kMaxNumTransponderPackets,
                                            .buffer = transponder_packet_reporting_queue_buffer_});

    // Public WiFi Settings
    char wifi_ssid[SettingsManager::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_password[SettingsManager::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.

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

    bool ReportRaw(SettingsManager::SerialInterface iface, const DecodedTransponderPacket packets_to_report[],
                   uint16_t num_packets_to_report);

    /**
     * Sends out Mode S Beast formatted transponder data on the selected serial interface. Reports all transponder
     * packets in the provided packets_to_report array, which is used to allow printing arbitrary blocks of transponder
     * packets received via the CommsManager's built-in transponder_packet_reporting_queue_.
     * @param[in] iface SerialInterface to broadcase Mode S Beast messages on.
     * @param[in] packets_to_report Array of transponder packets to report.
     * @param[in] num_packets_to_report Number of packets to report from the packets_to_report array.
     * @retval True if successful, false if something broke.
     */
    bool ReportBeast(SettingsManager::SerialInterface iface, const DecodedTransponderPacket packets_to_report[],
                     uint16_t num_packets_to_report);

    /**
     * Sends a series of MAVLINK ADSB_VEHICLE messages on the selected serial interface, one for each tracked aircraft
     * in the aircraft dictionary, plus a MAVLINK MESSAGE_INTERVAL message used as a delimiter at the end of the train
     * of ADSB_VEHICLE messages.
     * @param[in] iface SerialInterface to broadcast MAVLINK messages on. Note that this gets cast to a MAVLINK channel
     * as a bit of a dirty hack under the hood, then un-cast back into a SerialInterface in the UART send function
     * within MAVLINK. Shhhhhhh it's fine for now.
     * @retval True if successful, false if something went sideways.
     */
    bool ReportMAVLINK(SettingsManager::SerialInterface iface);

    CommsManagerConfig config_;

    // Console Settings
    CppAT at_parser_;

    // Queue for holding new transponder packets before they get reported.
    DecodedTransponderPacket transponder_packet_reporting_queue_buffer_[ADSBee::kMaxNumTransponderPackets];

    // Reporting Settings
    uint32_t comms_uart_baudrate_ = SettingsManager::kDefaultCommsUARTBaudrate;
    uint32_t gnss_uart_baudrate_ = SettingsManager::kDefaultGNSSUARTBaudrate;
    SettingsManager::ReportingProtocol
        reporting_protocols_[SettingsManager::SerialInterface::kNumSerialInterfaces - 1] = {
            SettingsManager::ReportingProtocol::kNoReports,
            SettingsManager::ReportingProtocol::kMAVLINK1};  // GNSS_UART not included.

    // private WiFi Settings
    bool wifi_enabled_ = false;
};

extern CommsManager comms_manager;
extern const CppAT::ATCommandDef_t at_command_list[];  // Initialized in comms_at.cc
extern const uint16_t at_command_list_num_commands;

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
#define CONSOLE_INFO(format, ...) \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kInfo, format "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_WARNING(format, ...)                                         \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kWarnings, \
                                       TEXT_COLOR_YELLOW format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_ERROR(format, ...)                                         \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kErrors, \
                                       TEXT_COLOR_RED format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */