#pragma once

extern "C" {
#include <ti/drivers/UART2.h>
#include <ti/drivers/dpl/ClockP.h>

#include "ti_drivers_config.h"
}

#include <cstdarg>  // For debug printf.
#include <cstdio>   // Regular pico/stdio.h doesn't support vprint functions.

#include "aircraft_dictionary_config.hh"
#include "bsp.hh"
#include "composite_array.hh"
#include "cpp_at.hh"
#include "settings.hh"

class CommsManager {
   public:
    static constexpr uint16_t kModeSPacketReportingQueueDepth = 100;
    static constexpr uint16_t kUATADSBPacketReportingQueueDepth = 50;
    // 16 ground stations deliver up to 16 uplinks/sec bunched into the ~176ms UAT ground segment;
    // depth 8 covers a full 50ms reporting check interval of back-to-back slots (~580B per entry).
    static constexpr uint16_t kUATUplinkPacketReportingQueueDepth = 8;

    static constexpr uint16_t kATCommandBufMaxLen = 1000;
    static constexpr uint16_t kPrintfBufferMaxSize = 1000;

    struct CommsManagerConfig {
        uint8_t uart_index = bsp.kSubGUARTIndex;
        uint32_t uart_baud_rate = SettingsManager::Settings::kDefaultUARTBaudRate;
        uint32_t uart_timeout_us = 0;  // Timeout for blocking reads, in microseconds.
    };

    // Console baud rates selectable via AT+BAUD_RATE. The stored rate is applied at boot by
    // SettingsManager::Apply() and persisted via AT+SETTINGS=SAVE; the default is
    // SettingsManager::Settings::kDefaultUARTBaudRate (1,000,000).
    static constexpr uint32_t kAllowedBaudRates[] = {115200, 230400, 460800, 921600, 1000000};

    static inline bool IsAllowedBaudRate(uint32_t baud) {
        for (uint32_t allowed : kAllowedBaudRates) {
            if (baud == allowed) return true;
        }
        return false;
    }

    CommsManager(CommsManagerConfig config);

    bool Init();
    bool Update();

    /**
     * Quiesces the console UART so the MCU can enter STANDBY. UART2_rxEnable() holds a
     * PowerCC26XX_DISALLOW_STANDBY power constraint the entire time RX is enabled; Suspend() disables
     * RX to release it. TX is unaffected, so console logging still works. Pair with Resume() on wake.
     * @retval True if the UART RX was disabled successfully, false otherwise.
     */
    bool Suspend();

    /**
     * Re-arms console UART reception after a Suspend()/STANDBY cycle. The UART peripheral itself is
     * saved/restored across STANDBY by the driver's Power notify hooks; only RX-enable is re-asserted.
     * @retval True if the UART RX was re-enabled successfully, false otherwise.
     */
    bool Resume();

    /**
     * Blocks until all queued console TX bytes have physically left the wire. Two stages are needed:
     * the write callback fires on DMA completion, but up to a FIFO's worth of bytes can still be
     * shifting out afterwards. Callers that need the line truly idle -- a baud change, or entering
     * STANDBY (UART2 holds a PowerCC26XX_DISALLOW_STANDBY constraint until its EOT interrupt, which
     * lands after the last stop bit) -- must wait for both.
     * @param[in] timeout_ms Budget for each stage separately, so a slow first stage cannot starve the
     *                       second and a wedged UART cannot hang the caller; the worst case for the
     *                       call as a whole is therefore 2 * timeout_ms. The default covers a full
     *                       kPrintfBufferMaxSize chunk (~87 ms at 115200).
     * @retval True if the line went idle, false if the timeout expired first.
     */
    bool DrainConsoleTx(uint32_t timeout_ms = 200);

    /**
     * Change the console UART baud rate at runtime. TI's UART2 driver has no live baud-change API, so
     * the UART is closed and reopened. Blocks until all pending TX bytes (including any response
     * already queued at the old baud) have left the wire before switching, so the host reads them
     * intact. RAM-only until persisted with AT+SETTINGS=SAVE; SettingsManager::Apply() re-applies the
     * stored rate at boot.
     * @param[in] baud New baud rate; must be one of kAllowedBaudRates.
     * @retval True if the baud rate was changed, false if baud was invalid.
     */
    bool SetBaudRate(uint32_t baud);

    inline uint32_t GetBaudRate() const { return config_.uart_baud_rate; }

    CPP_AT_CALLBACK(ATBaudRateCallback);
    CPP_AT_CALLBACK(ATBootUARTBootloaderCallback);
    CPP_AT_CALLBACK(ATDeviceInfoCallback);
    CPP_AT_HELP_CALLBACK(ATOTAHelpCallback);
    CPP_AT_CALLBACK(ATR1090GainCallback);
    CPP_AT_CALLBACK(ATLogLevelCallback);
    CPP_AT_CALLBACK(ATMAVLINKIDCallback);
    CPP_AT_CALLBACK(ATR1090PreambleCallback);
    CPP_AT_CALLBACK(ATR1090RxBoostCallback);
    CPP_AT_CALLBACK(ATProtocolOutCallback);
    CPP_AT_HELP_CALLBACK(ATProtocolOutHelpCallback);
    CPP_AT_CALLBACK(ATRebootCallback);
    CPP_AT_CALLBACK(ATRxEnableCallback);
    CPP_AT_HELP_CALLBACK(ATRxEnableHelpCallback);
    CPP_AT_CALLBACK(ATRxPositionCallback);
    CPP_AT_CALLBACK(ATRxStatsCallback);
    CPP_AT_CALLBACK(ATSettingsCallback);
    CPP_AT_CALLBACK(ATUptimeCallback);
    CPP_AT_CALLBACK(ATWatchdogCallback);
#ifdef HARDWARE_UNIT_TESTS
    CPP_AT_CALLBACK(ATTxCWCallback);
    CPP_AT_CALLBACK(ATRxCWCallback);
#endif

    int console_printf(const char* format, ...);
    int console_level_printf(SettingsManager::LogLevel level, const char* format, ...);
    int console_vprintf(const char* format, va_list args);

    int iface_printf(SettingsManager::SerialInterface iface, const char* format, ...);
    int iface_vprintf(SettingsManager::SerialInterface iface, const char* format, va_list args);
    bool iface_write(SettingsManager::SerialInterface iface, const void* buf, size_t len, bool blocking = false);
    bool iface_putc(SettingsManager::SerialInterface iface, char c, bool blocking = false);
    bool iface_getc(SettingsManager::SerialInterface iface, char& c);
    bool iface_puts(SettingsManager::SerialInterface iface, const char* buf, bool blocking = false);

#include "comms_reporting.hh"

    // num_packets is the number of report frames batched into buf; it is only meaningful for
    // network-feed platforms (which override SendBuf to do feed framing). On this serial platform
    // the bytes are written verbatim, so the count is ignored.
    inline bool SendBuf(ReportSink sink, const char* buf, uint16_t buf_len, uint16_t num_packets = 1) {
        (void)num_packets;
        return iface_write(static_cast<SettingsManager::SerialInterface>(sink), buf, buf_len);
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

    PFBQueue<RawModeSPacket> mode_s_packet_reporting_queue = PFBQueue<RawModeSPacket>(
        {.buf_len_num_elements = kModeSPacketReportingQueueDepth, .buffer = mode_s_packet_reporting_queue_buffer_});
    PFBQueue<RawUATADSBPacket> uat_adsb_packet_reporting_queue = PFBQueue<RawUATADSBPacket>(
        {.buf_len_num_elements = kUATADSBPacketReportingQueueDepth, .buffer = uat_adsb_packet_reporting_queue_buffer_});
    PFBQueue<RawUATUplinkPacket> uat_uplink_packet_reporting_queue =
        PFBQueue<RawUATUplinkPacket>({.buf_len_num_elements = kUATUplinkPacketReportingQueueDepth,
                                      .buffer = uat_uplink_packet_reporting_queue_buffer_});

   private:
    // AT Functions
    bool UpdateAT();

    // Opens the console UART at the given baud rate and enables RX. Used by Init() and SetBaudRate().
    bool OpenUART(uint32_t baud);

    CommsManagerConfig config_;

    // Console Settings
    CppAT at_parser_;

    UART2_Handle uart_handle_;
    volatile bool uart_tx_busy_ = false;
    char uart_tx_buf_[kPrintfBufferMaxSize];
    static void uart_write_callback(UART2_Handle handle, void* buf, size_t count, void* userArg, int_fast16_t status);

    // Queue for holding new transponder packets before they get reported.
    RawModeSPacket mode_s_packet_reporting_queue_buffer_[kModeSPacketReportingQueueDepth];
    RawUATADSBPacket uat_adsb_packet_reporting_queue_buffer_[kUATADSBPacketReportingQueueDepth];
    RawUATUplinkPacket uat_uplink_packet_reporting_queue_buffer_[kUATUplinkPacketReportingQueueDepth];

    // Reporting protocol timestamps
    // NOTE: Raw reporting interval used for RAW and BEAST protocols as well as internal functions.
    uint32_t last_raw_report_check_timestamp_ms_ =
        0;  // Timestamp of last time we checked whether we need to report packets.
    uint32_t last_raw_report_timestamp_ms_ = 0;
    // Single shared timer for all locally-decoded dictionary report protocols (CSBee, MAVLINK, GDL90).
    // All protocols share a UID snapshot and therefore share a reporting interval.
    uint32_t last_locally_decoded_report_timestamp_ms_ = 0;

    // Shared UID snapshot for all periodic dictionary reporting protocols.
    // One array avoids duplicating 800 bytes per protocol. UpdateReporting populates it once
    // per round; each protocol walks it independently via its own index below.
    uint32_t report_uids_[kMaxReportUIDs];
    uint16_t report_uids_count_ = 0;

    // Per-protocol progress indices into report_uids_[].
    uint16_t csbee_report_uid_index_ = 0;
    uint16_t mavlink1_report_uid_index_ = 0;
    uint16_t mavlink2_report_uid_index_ = 0;
    uint16_t gdl90_report_uid_index_ = 0;
    uint16_t aircraftjson_report_uid_index_ = 0;

    // Per-protocol "round active" flags. Set by UpdateReporting when a new round starts;
    // cleared by each Report* function when it finishes sending its footer/delimiter.
    bool csbee_round_active_ = false;
    bool mavlink1_round_active_ = false;
    bool mavlink2_round_active_ = false;
    bool gdl90_round_active_ = false;
    bool aircraftjson_round_active_ = false;

    // Overrun error gates — each fires once per overrunning round to prevent log spam.
    bool csbee_overrun_reported_ = false;
    bool mavlink1_overrun_reported_ = false;
    bool mavlink2_overrun_reported_ = false;
    bool gdl90_overrun_reported_ = false;
    bool aircraftjson_overrun_reported_ = false;
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
