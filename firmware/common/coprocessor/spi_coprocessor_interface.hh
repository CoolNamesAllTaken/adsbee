#pragma once

#include "object_dictionary.hh"
#include "spi_coprocessor_packet.hh"

#ifdef ON_PICO
#include <functional>  // For std::function.

#include "bsp.hh"
#include "hardware/gpio.h"
#include "hardware/spi.h"
#elif defined(ON_ESP32)
#include "bsp.hh"
#include "data_structures.hh"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#endif

class SPICoprocessorInterface {
   public:
    static constexpr uint16_t kErrorMessageMaxLen = 500;
    enum ReturnCode : int {
        kOk = 0,  // All good.
        kErrorGeneric = -1,
        kErrorTimeout = -2,
        kErrorHandshakeHigh = -3  // Used on the Master to indicate that a transaction was aborted because the slave was
                                  // tryingto talk at the same time as the master.
    };

    /**
     * Convert a ReturnCode to a human-readable string.
     * @param[in] code The ReturnCode to convert.
     * @retval String representation of the ReturnCode.
     */
    static const char *ReturnCodeToString(ReturnCode code) {
        switch (code) {
            case kOk:
                return "OK";
            case kErrorGeneric:
                return "Generic Error";
            case kErrorTimeout:
                return "Timeout Error";
            case kErrorHandshakeHigh:
                return "Handshake High Error";
            default:
                return "Unknown Error";
        }
    }

    /**
     * Initialize the SPI coprocessor interface.
     * @retval True if initialization was successful, false otherwise.
     */
    virtual bool Init() = 0;

    /**
     * Deinitialize the SPI coprocessor interface.
     * @retval True if deinitialization was successful, false otherwise.
     */
    virtual bool DeInit() = 0;

    virtual int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf,
                                     uint16_t len_bytes = SPICoprocessorPacket::kSPITransactionMaxLenBytes,
                                     bool end_transaction = true) = 0;
};

/**
 * Abstract interface for interacting with a SPI coprocessor master. For instance, this is used to interact with the
 * RP2040 (coprocessor master) on the ESP32 (coprocessor slave).
 */
class SPICoprocessorMasterInterface : public SPICoprocessorInterface {
   public:
    /**
     * Determine whether the handshake pin will be used during the next SPI transaction to solicit a response.
     * @param[in] level True to set pin high once SPI peripheral is loaded up, false to set pin low.
     */
    virtual inline void SPIUseHandshakePin(bool level) = 0;

    virtual inline void UpdateNetworkLED() = 0;

    virtual bool SPIBeginTransaction() = 0;
    virtual void SPIEndTransaction() = 0;
};

class SPICoprocessorSlaveInterface : public SPICoprocessorInterface {
   public:
    // Wait this long after a transmission is complete before allowing the HANDSHAKE line to override the minimum
    // transmit interval timeout. This ensures that we don't double-transmit to the slave before it has a chance to
    // lower the HANDSHAKE line following a transaction.
    static constexpr uint32_t kSPIPostTransmitLockoutUs = 10;
    // How long we pull the CS line LO before transmitting. If the handshake line goes high during this interval, we can
    // begin transmitting immediately.
    static constexpr uint32_t kSPIUpdateCSPreAssertIntervalUs = 100;
    // NOTE: Max transmission time is ~10ms with a 4kB packet at 40MHz.
    // How long to wait once a transaction is started before timing out.
    static constexpr uint32_t kSPITransactionTimeoutMs = 20;
    // How long a blocking wait for a handshake can last.
    static constexpr uint32_t kSPIHandshakeTimeoutMs = 20;
    // How long to loop in Update() for after initializing the device in order to allow it to query for settings data.
    static constexpr uint32_t kBootupDelayMs = 500;

    virtual bool Update() = 0;

    /**
     * Checks the level of the HANDSHAKE pin used to initiate communication from the ESP32 to RP2040.
     * NOTE: There is some hysteresis! The ESP32 can request a transfer as soon as kSPIPostTransmitLockoutUs is up, but
     * this function won't unblock and confidently state that the HANDSHAKE pin is not asserted unless
     * kSPIMinTransmitIntervalUs has elapsed.
     * @param[in] blocking If true, wait until the pin is readable before reading it (e.g. it's been long enough since
     * the end of the last transaction that the ESP32 has been able to assert or de-assert the HANDSHAKE pin as
     * necessary). If false, return false if kSPIPostTransmitLockoutUs has not elapsed, otherwise return the HANDSHAKE
     * pin state.
     */
    virtual bool SPIGetHandshakePinLevel(bool blocking = true) = 0;

    /**
     * Blocks on waiting for the handshake pin to go high, until a timeout is reached.
     * @retval True if handshake line went high before timeout, false otherwise.
     */
    inline bool SPIWaitForHandshake() {
        uint32_t wait_begin_timestamp_ms = get_time_since_boot_ms();
        expecting_handshake_ = true;  // Set this so that we know we are expecting the handshake line to go high.
        while (true) {
            if (SPIGetHandshakePinLevel(false)) {
                // Received handshake signal during non-blocking check.
                break;
            }
            if (get_time_since_boot_ms() - wait_begin_timestamp_ms >= kSPIHandshakeTimeoutMs) {
                // Timed out.
                expecting_handshake_ = false;  // Reset this so that we don't think we are expecting a handshake.
                return false;
            }
        }
        return true;
    }

    virtual bool IsEnabled() = 0;
    virtual void SetEnable(bool enabled) = 0;

    /**
     * Gets the timestamp of the last successful device status query from the ESP32.
     * @retval Timestamp in milliseconds since boot.
     */
    virtual uint32_t GetLastHeartbeatTimestampMs() = 0;

    virtual bool SPIBeginTransaction() = 0;
    virtual void SPIEndTransaction() = 0;

   protected:
    // Use this flag to indicate whether we are expecting the handshake line to go high. If it is high during a
    // transaction when we aren't expecting it, that means that we are stomping on the slave! Not good.
    bool expecting_handshake_ = false;
};