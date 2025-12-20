#pragma once

#include "composite_array.hh"
#include "cpp_at.hh"
#include "data_structures.hh"  // For PFBQueue.
#include "hardware/uart.h"
#include "mode_s_packet.hh"
#include "settings.hh"
#include "uat_packet.hh"

class CommsManager {
   public:
    static constexpr uint16_t kModeSPacketReportingQueueDepth = 100;
    static constexpr uint16_t kUATADSBPacketReportingQueueDepth = 50;
    static constexpr uint16_t kUATUplinkPacketReportingQueueDepth = 2;

    static constexpr uint16_t kATCommandBufMaxLen = 1000;
    static constexpr uint16_t kNetworkConsoleBufMaxLen = 4096;
    static constexpr uint16_t kNetworkConsoleReportingIntervalOverrideNumChars =
        kNetworkConsoleBufMaxLen * 3 /
        4;  // Drain the network console queue immediately if it has more than this many characters.
    static constexpr uint32_t kNetworkConsoleMinReportingIntervalMs =
        50;  // Report messages to nextwork console at minimum rate of 20Hz.
    static constexpr uint16_t kPrintfBufferMaxSize = 500;

    static constexpr uint32_t kOTAWriteTimeoutMs = 5000;  // ms until OTA write command exits if all bytes not received.

    struct CommsManagerConfig {
        uart_inst_t* comms_uart_handle = uart1;
        uint16_t comms_uart_tx_pin = 4;
        uint16_t comms_uart_rx_pin = 5;
        uart_inst_t* gnss_uart_handle = uart0;
        uint16_t gnss_uart_tx_pin = 0;
        uint16_t gnss_uart_rx_pin = 1;
        uint16_t uart_timeout_us = 0;  // Time to wait for a character if there isn't one alredy available.
    };

    CommsManager(CommsManagerConfig config_in);

    /**
     * Initialize the CommsManager. Sets up UARTs and other necessary peripherals.
     * @retval True if initialization succeeded, false otherwise.
     */
    bool Init();

    /**
     * Update the CommsManager. Runs all the update subroutines required for normal operation.
     * @retval True if update succeeded, false otherwise.
     */
    bool Update();

    /**
     * Update incoming and outgoing buffers for the ESP32 network console. Called as part of Update(), or can be called
     * separately if desired (e.g. while printing to the console without forwarding incoming data to the AT command
     * parser).
     * @retval True if update succeeded, false otherwise.
     */
    bool UpdateNetworkConsole();

    CPP_AT_CALLBACK(ATBaudRateCallback);
    CPP_AT_CALLBACK(ATBiasTeeEnableCallback);
    CPP_AT_CALLBACK(ATDeviceInfoCallback);
    CPP_AT_CALLBACK(ATESP32EnableCallback);
    CPP_AT_CALLBACK(ATESP32FlashCallback);
    CPP_AT_CALLBACK(ATEthernetCallback);
    CPP_AT_CALLBACK(ATFeedCallback);
    CPP_AT_CALLBACK(ATHostnameCallback);
    CPP_AT_CALLBACK(ATOTACallback);
    CPP_AT_HELP_CALLBACK(ATOTAHelpCallback);
    CPP_AT_CALLBACK(ATLogLevelCallback);
    CPP_AT_CALLBACK(ATMAVLINKIDCallback);
    CPP_AT_CALLBACK(ATNetworkInfoCallback);
    CPP_AT_CALLBACK(ATProtocolOutCallback);
    CPP_AT_HELP_CALLBACK(ATProtocolOutHelpCallback);
    CPP_AT_CALLBACK(ATRebootCallback);
    CPP_AT_CALLBACK(ATRxEnableCallback);
    CPP_AT_HELP_CALLBACK(ATRxEnableHelpCallback);
    CPP_AT_CALLBACK(ATRxPositionCallback);
    CPP_AT_CALLBACK(ATSettingsCallback);
    CPP_AT_CALLBACK(ATSubGEnableCallback);
    CPP_AT_CALLBACK(ATSubGFlashCallback);
    CPP_AT_CALLBACK(ATTLReadCallback);
    CPP_AT_CALLBACK(ATTLSetCallback);
    CPP_AT_CALLBACK(ATUptimeCallback);
    CPP_AT_CALLBACK(ATWatchdogCallback);
    CPP_AT_CALLBACK(ATWiFiAPCallback);
    CPP_AT_CALLBACK(ATWiFiSTACallback);

    int console_printf(const char* format, ...);
    int console_level_printf(SettingsManager::LogLevel level, const char* format, ...);
    int iface_printf(SettingsManager::SerialInterface iface, const char* format, ...);
    int iface_vprintf(SettingsManager::SerialInterface iface, const char* format, va_list args);
    bool iface_putc(SettingsManager::SerialInterface iface, char c);
    bool iface_getc(SettingsManager::SerialInterface iface, char& c);
    bool iface_puts(SettingsManager::SerialInterface iface, const char* buf);

    bool network_console_putc(char c);
    bool network_console_puts(const char* buf, uint16_t len = UINT16_MAX);

#include "comms_reporting.hh"

    inline bool SendBuf(ReportSink sink, const char* buf, uint16_t buf_len) {
        for (uint16_t i = 0; i < buf_len; i++) {
            if (!iface_putc(static_cast<SettingsManager::SerialInterface>(sink), buf[i])) {
                return false;
            }
        }
        return true;
    }

    /**
     * Sets the baudrate for a serial interface.
     * @param[in] iface SerialInterface to set baudrate for.
     * @param[in] baudrate Baudrate to set.
     * @retval True if the baudrate could be set, false if the interface specified does not support a baudrate.
     */
    inline bool SetBaudRate(SettingsManager::SerialInterface iface, uint32_t baudrate) {
        switch (iface) {
            case SettingsManager::kCommsUART:
                // Save the actual set valuecomms_uart_baud_rate as comms_uart_baudrate_.
                settings_manager.settings.baud_rates[SettingsManager::SerialInterface::kCommsUART] =
                    uart_set_baudrate(config_.comms_uart_handle, baudrate);
                return true;
                break;
            case SettingsManager::kGNSSUART:
                // Save the actual set value as gnss_uart_baudrate_.
                settings_manager.settings.baud_rates[SettingsManager::SerialInterface::kGNSSUART] =
                    uart_set_baudrate(config_.gnss_uart_handle, baudrate);
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
    inline bool GetBaudRate(SettingsManager::SerialInterface iface, uint32_t& baudrate) {
        switch (iface) {
            case SettingsManager::kCommsUART:
                // Save the actual set value as comms_uart_baudrate_.
                baudrate = settings_manager.settings.baud_rates[SettingsManager::SerialInterface::kCommsUART];
                return true;
                break;
            case SettingsManager::kGNSSUART:
                // Save the actual set value as gnss_uart_baudrate_.
                baudrate = settings_manager.settings.baud_rates[SettingsManager::SerialInterface::kGNSSUART];
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
    inline bool SetReportingProtocol(SettingsManager::SerialInterface iface,
                                     SettingsManager::ReportingProtocol protocol) {
        settings_manager.settings.reporting_protocols[iface] = protocol;
        return true;
    }

    /**
     * Get the reporting protocol for a given serial interface.
     * @param[in] iface SerialInterface to get the reporting protocol from.
     * @param[out] protocol reference to ReportingProtocol to fill with result.
     * @retval True if reportig protocol could be retrieved, false otherwise.
     */
    inline bool GetReportingProtocol(SettingsManager::SerialInterface iface,
                                     SettingsManager::ReportingProtocol& protocol) {
        protocol = settings_manager.settings.reporting_protocols[iface];
        return true;
    }

    // Queue for storing transponder packets before they get reported.
    PFBQueue<RawModeSPacket> mode_s_packet_reporting_queue = PFBQueue<RawModeSPacket>(
        {.buf_len_num_elements = kModeSPacketReportingQueueDepth, .buffer = mode_s_packet_reporting_queue_buffer_});
    PFBQueue<RawUATADSBPacket> uat_adsb_packet_reporting_queue = PFBQueue<RawUATADSBPacket>(
        {.buf_len_num_elements = kUATADSBPacketReportingQueueDepth, .buffer = uat_adsb_packet_reporting_queue_buffer_});
    PFBQueue<RawUATUplinkPacket> uat_uplink_packet_reporting_queue =
        PFBQueue<RawUATUplinkPacket>({.buf_len_num_elements = kUATUplinkPacketReportingQueueDepth,
                                      .buffer = uat_uplink_packet_reporting_queue_buffer_});

    // Queues for incoming / outgoing network characters.
    PFBQueue<char> esp32_console_rx_queue =
        PFBQueue<char>({.buf_len_num_elements = kNetworkConsoleBufMaxLen, .buffer = esp32_console_rx_queue_buffer_});
    PFBQueue<char> esp32_console_tx_queue =
        PFBQueue<char>({.buf_len_num_elements = kNetworkConsoleBufMaxLen, .buffer = esp32_console_tx_queue_buffer_});

   private:
    // AT Functions
    bool InitAT();
    bool UpdateAT();

    CommsManagerConfig config_;

    // Console Settings
    CppAT at_parser_;

    // Queues for incoming / outgoing network console characters.
    char esp32_console_rx_queue_buffer_[kNetworkConsoleBufMaxLen];
    char esp32_console_tx_queue_buffer_[kNetworkConsoleBufMaxLen];
    uint32_t last_esp32_console_tx_timestamp_ms_ = 0;  // Timestamp of last network console TX.

    // Queue for holding new transponder packets before they get reported.
    RawModeSPacket mode_s_packet_reporting_queue_buffer_[kModeSPacketReportingQueueDepth];
    RawUATADSBPacket uat_adsb_packet_reporting_queue_buffer_[kUATADSBPacketReportingQueueDepth];
    RawUATUplinkPacket uat_uplink_packet_reporting_queue_buffer_[kUATUplinkPacketReportingQueueDepth];

    // Reporting protocol timestamps
    // NOTE: Raw reporting interval used for RAW and BEAST protocols as well as internal functions.
    uint32_t last_raw_report_timestamp_ms_ = 0;
    uint32_t last_csbee_report_timestamp_ms_ = 0;
    uint32_t last_mavlink_report_timestamp_ms_ = 0;
    uint32_t last_gdl90_report_timestamp_ms_ = 0;
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
#define CONSOLE_INFO(tag, format, ...)                                                                         \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kInfo,                                       \
                                       tag ": " TEXT_COLOR_GREEN format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) \
                                           __VA_ARGS__);
#define CONSOLE_WARNING(tag, format, ...)                                                                       \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kWarnings,                                    \
                                       tag ": " TEXT_COLOR_YELLOW format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) \
                                           __VA_ARGS__);
#define CONSOLE_ERROR(tag, format, ...)                                        \
    comms_manager.console_level_printf(SettingsManager::LogLevel::kErrors, tag \
                                       ": " TEXT_COLOR_RED format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);
