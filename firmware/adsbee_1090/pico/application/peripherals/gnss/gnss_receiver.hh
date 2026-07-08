#pragma once

#include "bsp.hh"
#include "hardware/uart.h"  // For uart_inst_t and UART bring-up in Init().
#include "nmea_parser.hh"
#include "pico/stdlib.h"  // For gpio_* and tight_loop_contents() used by subclasses/impl.
#include "settings.hh"

/**
 * Abstract base class for a GNSS receiver that emits NMEA over UART.
 *
 * Owns the generic NMEA parser and the UART read loop, and manages the (optional) active-low
 * power-enable pin. Receiver-specific behavior (default baud rate, vendor configuration commands,
 * boot delay) is provided by subclasses (e.g. UbloxMAXM10).
 *
 * The GNSS UART itself is initialized once by CommsManager (see comms.cc). This class does NOT
 * re-initialize the UART; it reads/writes through CommsManager's kGNSSUART interface so all UART
 * ownership stays centralized.
 */
class GNSSReceiver {
   public:
    using GNSSFix = NMEAParser::GNSSFix;

    // A fix is considered current only if it was updated within this window.
    static constexpr uint32_t kFixStaleTimeoutMs = 5000;

    struct GNSSReceiverConfig {
        uart_inst_t* uart_handle = uart0;
        uint16_t uart_tx_pin = bsp.gnss_uart_tx_pin;  // GPIO 0
        uint16_t uart_rx_pin = bsp.gnss_uart_rx_pin;  // GPIO 1
        // Active-low high-side power switch for the module's VCC/VCC_IO. UINT16_MAX = not connected.
        uint16_t enable_pin = bsp.gnss_enable_pin;
        uint16_t pps_pin = bsp.gnss_pps_pin;
    };

    GNSSReceiver(GNSSReceiverConfig config_in) : config_(config_in) {}
    virtual ~GNSSReceiver() = default;

    /**
     * Power on the module (if an enable pin is connected), wait for it to boot, set the baud rate,
     * send receiver-specific configuration, and confirm the module is responding. Does not block
     * indefinitely and does not hard-fail if the module is absent or unresponsive.
     * @retval True if the module responded and was configured; false if absent/unresponsive (the
     *         system should fall back to its non-GNSS position source).
     */
    bool Init();

    /**
     * Drain available bytes from the GNSS UART and feed them to the NMEA parser. Call from the
     * main loop.
     * @retval True on success.
     */
    bool Update();

    /**
     * Enable or disable module power via the active-low enable pin. No-op if no enable pin.
     */
    void SetEnable(bool enabled);

    /**
     * @retval The most recently merged GNSS fix.
     */
    const GNSSFix& fix() const { return parser_.fix(); }

    /**
     * @retval True if the module is healthy AND has a valid, non-stale fix. This is the single
     *         signal the application uses to decide whether GNSS position is usable.
     */
    bool HasValidFix() const;

    /**
     * @retval True if the module responded during Init() (i.e. it is present and configured).
     */
    bool IsHealthy() const { return healthy_; }

   protected:
    /**
     * @retval Receiver-specific default UART baud rate (e.g. factory default for the module).
     */
    virtual uint32_t GetDefaultBaudrate() const = 0;

    /**
     * Time to wait after powering the module before it is ready to accept configuration. Differs
     * between receivers, hence virtual.
     */
    virtual uint32_t GetBootDelayMs() const = 0;

    /**
     * Send receiver-specific configuration (e.g. UBX-CFG-VALSET for u-blox). Called by Init()
     * after the boot delay.
     * @retval True if the module acknowledged configuration (also used as the liveness check).
     */
    virtual bool SendInitCommands() = 0;

    // TEMPORARY debug hooks (remove with the rest of the GNSS debug instrumentation).
    // DebugIngestByte: fed every received UART byte so a concrete receiver can passively sniff its
    // binary protocol (e.g. ublox UBX) from the same stream the NMEA parser consumes.
    // DebugDumpModuleStatus: prints the latest sniffed module diagnostics. Defaults no-op.
    virtual void DebugIngestByte(char c) { (void)c; }
    virtual void DebugDumpModuleStatus() {}

    GNSSReceiverConfig config_;
    NMEAParser parser_;
    bool healthy_ = false;

    // TEMPORARY debug instrumentation for diagnosing "GNSS NOT AVAILABLE". Remove once root cause
    // is found. Tracks whether bytes are arriving and what the parser is producing.
    static constexpr uint32_t kDebugPrintIntervalMs = 2000;
    static constexpr uint32_t kDebugRfDumpIntervalMs = 10000;  // MON-RF poll competes with NMEA drain; throttle harder.
    uint32_t debug_total_rx_bytes_ = 0;
    uint32_t debug_gga_count_ = 0;
    uint32_t debug_rmc_count_ = 0;
    uint32_t debug_cksum_fail_count_ = 0;
    NMEAParser::SentenceType debug_last_sentence_ = NMEAParser::kSentenceNone;
    uint32_t debug_last_print_timestamp_ms_ = 0;
    uint32_t debug_last_rf_dump_timestamp_ms_ = 0;
};
