#pragma once

#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_packet.hh"
#include "ti/drivers/SPI.h"
#include "ti/drivers/GPIO.h"

class Pico : public SPICoprocessorMasterInterface
{
public:
    static constexpr uint32_t kNetworkLEDBlinkDurationMs = 1;

    // Since the transaction timeout value is used by threads waiting to use the SPI peripheral, and the SPI update task
    // blocks the copro_spi_mutex_ until it receives a transfer from the master, this timeout needs to be set to the
    // maximum delay between unsolicited packets from the master (heartbeat) to avoid threads giving up while the SPI
    // update task is hogging the mutex.
    // How long to wait once a transaction is started before timing out.
    static constexpr uint16_t kSPITransactionTimeoutMs = 200;

    static constexpr uint16_t kSPIMutexTimeoutMs =
        1200; // How long to wait for the transaction mutex before timing out.

    enum SPITransactionError : int
    {
        kSPITransactionErrorReturnedFalse = -1,
        kSPITransactionErrorLengthIncorrect = -2
    };

    struct PicoConfig
    {
        uint16_t spi_handshake_pin = bsp.kSubGIRQPin; // Pin used to signal the ESP32 that a transaction is ready.

        uint16_t network_led_pin = bsp.kSubGLEDPin; // Pin used to blink the network LED on successful transactions.
    };

    Pico(PicoConfig config_in);
    ~Pico();

    bool Init();
    bool DeInit();

    /**
     * Helper function used by callbacks to set the handshake pin high or low on the ESP32.
     * Located in IRAM for performance improvements when called from ISR.
     */
    inline void SetSPIHandshakePinLevel(bool level)
    {
        // Only set the handshake pin HI when we know we want to solicit a response and not block + wait.
        // Handshake pin can always be set LO.
        GPIO_write(config_.spi_handshake_pin, level && use_handshake_pin_);
    }

    inline void SPIUseHandshakePin(bool level) { use_handshake_pin_ = level; }

    inline bool SPIBeginTransaction()
    {
        last_bytes_transacted_ = 0; // Reset the last bytes transacted counter.
        return true;
    }
    inline void SPIEndTransaction()
    {
        // xSemaphoreGive(spi_mutex_);
        if (last_bytes_transacted_ > 0)
        {
            BlinkNetworkLED(); // Blink the network LED to indicate a successful transaction.
        }
    }

    bool SPIWriteNonBlocking(uint8_t *tx_buf,
                             uint16_t len_bytes = SPICoprocessorPacket::kSPITransactionMaxLenBytes);

    /**
     * Function called from the task spawned during Init().
     */
    void SPIReceiveTask();

    /**
     * Turns on the network LED for a specified number of milliseconds. Relies on the UpdateNetowrkLED() function to
     * turn the lED off.
     * @param[in] blink_duration_ms Number of milliseconds that the LED should stay on for.
     */
    inline void BlinkNetworkLED(uint16_t blink_duration_ms = kNetworkLEDBlinkDurationMs)
    {
        GPIO_write(config_.network_led_pin, 1);
        network_led_turn_on_timestamp_ms_ = get_time_since_boot_ms();
        network_led_on = true;
    }

    /**
     * Turns off the network LED if necessary.
     */
    inline void UpdateNetworkLED()
    {
        if (network_led_on &&
            get_time_since_boot_ms() - network_led_turn_on_timestamp_ms_ > kNetworkLEDBlinkDurationMs)
        {
            GPIO_write(config_.network_led_pin, 0);
            network_led_on = false;
        }
    }

    bool SPIPostTransactionCallback();

private:
    void SPIResetTransaction();

    PicoConfig config_; // Configuration for the RP2040 SPI coprocessor master interface.
    // SemaphoreHandle_t spi_mutex_;                  // Low level mutex used to guard the SPI peripheral (don't let multiple
    //                                                // threads queue packets at the same time).
    // SemaphoreHandle_t spi_next_transaction_mutex_; // High level mutex used to claim the next transaction interval.

    // SPI peripheral needs to operate on special buffers that are 32-bit word aligned and in DMA accessible memory.
    uint8_t spi_rx_buf_[SPICoprocessorPacket::kSPITransactionMaxLenBytes] = {0};
    uint8_t spi_tx_buf_[SPICoprocessorPacket::kSPITransactionMaxLenBytes] = {0};

    SPI_Handle spi_handle_ = nullptr; // Handle to the SPI peripheral used by the RP2040 SPI coprocessor master interface.
    SPI_Transaction spi_transaction_ = {
        .count = SPICoprocessorPacket::kSPITransactionMaxLenBytes,
        .txBuf = &spi_tx_buf_,
        .rxBuf = &spi_rx_buf_,
        .arg = nullptr}; // SPI transaction used to send and receive data from the SPI peripheral.
    uint16_t spi_transaction_len_bytes_ = 0; // Length of the pending SPI transaction in bytes. Allows the callback function to figure out how long the transaction was supposed to be.

    bool spi_receive_task_should_exit_ = false; // Flag used to tell SPI receive task to exit.
    uint32_t network_led_turn_on_timestamp_ms_ = 0;
    bool network_led_on = false;
    bool use_handshake_pin_ =
        false;                      // Allow handshake pin toggle to be skipped if waiting for a mesage and not writing to master.
    int last_bytes_transacted_ = 0; // Used to determine whether the last transaction was successful.
};

extern Pico pico_ll; // Global instance of the RP2040 SPI coprocessor master interface.