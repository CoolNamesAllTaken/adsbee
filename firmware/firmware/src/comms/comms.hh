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

    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t { kConsole = 0, kCommsUART, kGNSSUART, kNumSerialInterfaces };
    static const uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char SerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum ATConfigMode : uint16_t { kRun = 0, kConfig = 1, kInvalid = 2 };

    // Reporting Protocol enum and string conversion array.
    enum ReportingProtocol : uint16_t { kNone = 0, kRaw, kRawValidated, kMAVLINK, kGDL90, kNumProtocols };
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
    };

    CommsManager(CommsManagerConfig config_in);
    bool Init();
    bool Update();

    CPP_AT_CALLBACK(ATBaudrateCallback);
    CPP_AT_CALLBACK(ATConfigCallback);
    CPP_AT_CALLBACK(ATProtocolCallback);
    CPP_AT_CALLBACK(ATRxGainCallback);
    CPP_AT_CALLBACK(ATSettingsCallback);
    CPP_AT_CALLBACK(ATTLReadCallback);
    CPP_AT_CALLBACK(ATTLSetCallback);

    int console_printf(const char *format, ...);
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

   private:
    // AT Functions
    bool InitAT();
    bool UpdateAT();

    // Reporting Functions
    bool InitReporting();
    bool UpdateReporting();
    bool ReportMAVLINK(SerialInterface iface);

    CommsManagerConfig config_;

    // AT Settings
    CppAT at_parser_;
    ATConfigMode at_config_mode_ = ATConfigMode::kRun;

    // Reporting Settings
    uint32_t comms_uart_baudrate_ = kDefaultCommsUARTBaudrate;
    uint32_t gnss_uart_baudrate_ = kDefaultGNSSUARTBaudrate;
    ReportingProtocol reporting_protocols_[SerialInterface::kNumSerialInterfaces - 1] = {
        ReportingProtocol::kNone, ReportingProtocol::kMAVLINK};  // GNSS_UART not included.
};

extern CommsManager comms_manager;

#define CONSOLE_PRINTF(format, ...) comms_manager.console_printf(format __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */