#pragma once

#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_packet.hh"

extern "C"
{
#include "ti/drivers/SPI.h"
#include "ti/drivers/GPIO.h"
}

// // Include TI's memory utilities
// #include "ti/drivers/dma/UDMACC26XX.h"

class Pico : public SPICoprocessorMasterInterface
{
public:
    static constexpr uint32_t kSubGLEDBlinkDurationMs = 1;

    static const uint16_t kSPITransactionMaxLenBytes = SPICoprocessorPacket::kSPITransactionMaxLenBytes; // Normally set to SPICoprocessorPacket::kSPITransactionMaxLenBytes, but can be set to a lower value for testing purposes.

    enum SPITransactionError : int
    {
        kSPITransactionErrorReturnedFalse = -1,
        kSPITransactionErrorLengthIncorrect = -2
    };

    struct PicoConfig
    {
        uint16_t spi_handshake_pin = bsp.kSubGIRQPin; // Pin used to signal the ESP32 that a transaction is ready.

        uint16_t subg_led_pin = bsp.kSubGLEDPin; // Pin used to blink the network LED on successful transactions.
    };

    Pico(PicoConfig config_in);
    ~Pico();

    bool Init();
    bool DeInit();

    /**
     * Helper function used by callbacks to set the handshake pin high or low.
     */
    inline void SetSPIHandshakePinLevel(bool level)
    {
        // Only set the handshake pin HI when we know we want to solicit a response and not block + wait.
        // Handshake pin is active LO.

        GPIO_write(config_.spi_handshake_pin, !level);
    }

    inline void SPIUseHandshakePin(bool level) { use_handshake_pin_ = level; }
    inline bool SPIIsUsingHandshakePin() const { return use_handshake_pin_; }

    bool SPIBeginTransaction();
    void SPIEndTransaction();

    bool SPIWriteNonBlocking(uint8_t *tx_buf,
                             uint16_t len_bytes = SPICoprocessorPacket::kSPITransactionMaxLenBytes);

    bool SPIProcessTransaction();
    void SPIResetTransaction();

#ifndef ON_TI
    /**
     * Function called from the task spawned during Init().
     */
    void SPIReceiveTask();
#endif // ON_TI

    /**
     * Turns on the network LED for a specified number of milliseconds. Relies on the UpdateNetowrkLED() function to
     * turn the lED off.
     * @param[in] blink_duration_ms Number of milliseconds that the LED should stay on for.
     */
    inline void BlinkSubGLED(uint16_t blink_duration_ms = kSubGLEDBlinkDurationMs)
    {
        GPIO_write(config_.subg_led_pin, 1);
        subg_led_turn_on_timestamp_ms_ = get_time_since_boot_ms();
        subg_led_on = true;
    }

    /**
     * Turns off the network LED if necessary.
     */
    inline void UpdateLED()
    {
        if (subg_led_on &&
            get_time_since_boot_ms() - subg_led_turn_on_timestamp_ms_ > kSubGLEDBlinkDurationMs)
        {
            GPIO_write(config_.subg_led_pin, 0);
            subg_led_on = false;
        }
    }

private:
    PicoConfig config_; // Configuration for the RP2040 SPI coprocessor master interface.
                        // SemaphoreHandle_t spi_mutex_;                  // Low level mutex used to guard the SPI peripheral (don't let multiple
                        //                                                // threads queue packets at the same time).
                        // SemaphoreHandle_t spi_next_transaction_mutex_; // High level mutex used to claim the next transaction interval.

    volatile uint8_t spi_rx_buf_[kSPITransactionMaxLenBytes];
    volatile uint8_t spi_tx_buf_[kSPITransactionMaxLenBytes];
    volatile SPI_Transaction spi_transaction_ = {
        // SPI transaction used to send and receive data from the SPI peripheral.
        .count = 0,
        .txBuf = (void *)spi_tx_buf_,
        .rxBuf = (void *)spi_rx_buf_,
        .arg = nullptr};

    SPI_Params spi_params_;
    SPI_Handle spi_handle_ = nullptr; // Handle to the SPI peripheral used by the RP2040 SPI coprocessor master interface.
    // static SPI_Transaction spi_transaction_; // SPI transaction used to send and receive data from the SPI peripheral.
    uint16_t spi_transaction_len_bytes_ = 0; // Length of the pending SPI transaction in bytes. Allows the callback function to figure out how long the transaction was supposed to be.

    bool spi_receive_task_should_exit_ = false; // Flag used to tell SPI receive task to exit.
    uint32_t subg_led_turn_on_timestamp_ms_ = 0;
    bool subg_led_on = false;
    bool use_handshake_pin_ =
        false;                      // Allow handshake pin toggle to be skipped if waiting for a mesage and not writing to master.
    int last_bytes_transacted_ = 0; // Used to determine whether the last transaction was successful.
};

extern Pico pico_ll; // Global instance of the RP2040 SPI coprocessor master interface.