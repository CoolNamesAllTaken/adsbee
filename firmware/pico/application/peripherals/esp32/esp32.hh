#pragma once

#include "bsp.hh"
#include "hardware/spi.h"
#include "spi_coprocessor.hh"

// Uncomment this to forward log messages overs SPI from the ESP32.
// #define PULL_ESP32_LOG_MESSAGES

class ESP32 : public SPICoprocessorSlaveInterface {
   public:
    static const uint16_t kDeviceStatusUpdateDefaultIntervalMs = 200;  // 5Hz updates by default.
    static const uint16_t kMaxNumSCCommandRequestsPerUpdate = 5;
    static const uint32_t kBootupDelayMs = 500;  // Delay after enabling the ESP32 before starting comms.

    struct ESP32Config {
        uint16_t enable_pin = bsp.esp32_enable_pin;
        spi_inst_t *spi_handle = bsp.copro_spi_handle;
        uint16_t spi_cs_pin = bsp.esp32_spi_cs_pin;
        uint16_t spi_handshake_pin = bsp.esp32_spi_handshake_pin;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;
    };

    ESP32(ESP32Config config_in);

    bool Init();
    bool DeInit();

    /**
     * Updates the ESP32 peripheral, including querying device status, processing any pending SCCommand requests, and
     * pulling logs (if enabled).
     * @retval True if successful, false if there was an error.
     */
    bool Update();

    /**
     * Executes a single SCCommand request received from the ESP32.
     * @param[in] request The SCCommandRequest to execute.
     * @retval True if the command was executed successfully, false otherwise.
     */
    bool ExecuteSCCommandRequest(const ObjectDictionary::SCCommandRequest &request);

    /**
     * Gets the timestamp of the last successful device status query from the ESP32.
     * @retval Timestamp in milliseconds since boot.
     */
    inline uint32_t GetLastHeartbeatTimestampMs() { return last_device_status_update_timestamp_ms_; }

    inline bool IsEnabled() { return enabled_; }
    inline void SetEnable(bool enabled) {
        gpio_put(config_.enable_pin, enabled);
        enabled_ = enabled;
    }

    inline bool SPIBeginTransaction() {
        gpio_put(config_.spi_cs_pin, 0);
        return true;
    }
    inline void SPIEndTransaction() {
        expecting_handshake_ = false;  // Reset the handshake expectation after a transaction.
        gpio_put(config_.spi_cs_pin, 1);
        spi_last_transmit_timestamp_us_ = get_time_since_boot_us();
    }
    bool SPIGetHandshakePinLevel(bool blocking = true);

    int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf,
                             uint16_t len_bytes = SPICoprocessorPacket::kSPITransactionMaxLenBytes,
                             bool end_transaction = true);

    uint32_t device_status_update_interval_ms =
        kDeviceStatusUpdateDefaultIntervalMs;  // Interval for device status updates.

   private:
    ESP32Config config_;
    bool enabled_ = false;
    uint64_t spi_last_transmit_timestamp_us_ = 0;  // Timestamp of the end of the last SPI transaction.

    uint32_t last_device_status_update_timestamp_ms_ = 0;  // Timestamp of the last device status update.
};

extern ESP32 esp32_ll;