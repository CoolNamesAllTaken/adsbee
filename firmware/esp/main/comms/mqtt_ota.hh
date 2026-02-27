#pragma once

#include "mqtt_config.h"
#include <cstdint>
#include <cstddef>
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"

class ADSBeeMQTTClient;

/**
 * Lightweight MQTT OTA shim.
 *
 * Bridges MQTT OTA messages into the existing CLI OTA flow by pushing
 * AT+OTA commands and binary data into the network_console_rx_queue.
 * The Pico handles all flash operations, CRC verification, and boot.
 *
 * Uses the console_intercept_callback in ObjectDictionary to capture Pico
 * responses (OK/ERROR/READY) and implement ACK-based flow control that
 * the publisher script relies on.
 *
 * ERASE is non-blocking so the MQTT keepalive is not disrupted.
 * After all chunks are written, auto-verifies and transitions to READY_TO_BOOT.
 */
class MQTTOTAHandler {
public:
    MQTTOTAHandler(const char* device_id, uint16_t feed_index);
    ~MQTTOTAHandler();

    bool Initialize(ADSBeeMQTTClient* mqtt_client);

    /// Handle incoming MQTT messages routed from ADSBeeMQTTClient
    bool HandleManifest(const uint8_t* data, size_t len);
    bool HandleCommand(const uint8_t* data, size_t len);
    bool HandleChunk(uint32_t chunk_index, const uint8_t* data, size_t len);

    bool IsActive() const { return active_; }

private:
    /// Push an AT command string into the network console RX queue
    bool SendCommandToPico(const char* cmd);

    /// Push raw binary data into the network console RX queue (flow-controlled)
    bool SendDataToPico(const uint8_t* data, size_t len);

    /// Wait for Pico response containing expected_str, up to timeout_ms
    bool WaitForPicoResponse(const char* expected_str, uint32_t timeout_ms);

    /// Publish JSON state to MQTT status topic
    void PublishState(const char* state, const char* detail = nullptr);

    /// Publish chunk ACK to MQTT
    void PublishChunkAck(uint32_t chunk_index, bool success);

    /// Simple JSON helpers (no std::string)
    static bool ParseJsonString(const char* json, size_t json_len,
                                const char* key, char* buf, size_t buf_size);
    static bool ParseJsonUint32(const char* json, size_t json_len,
                                const char* key, uint32_t* out);

    /// Console intercept callback (called from SPI receive task context)
    static void ConsoleInterceptCb(const char* data, size_t len);
    void OnConsoleData(const char* data, size_t len);

    ADSBeeMQTTClient* mqtt_client_ = nullptr;
    char device_id_[32] = {};
    uint16_t feed_index_ = 0;
    bool active_ = false;

    // Manifest metadata
    uint32_t total_size_ = 0;
    uint32_t chunk_size_ = 0;
    uint32_t total_chunks_ = 0;
    char session_id_[48] = {};
    uint32_t session_id32_ = 0;

    // Progress
    uint32_t chunks_received_ = 0;

    // Non-blocking erase state
    bool erase_pending_ = false;  // True while waiting for Pico ERASE OK

    // Response interception
    SemaphoreHandle_t response_sem_ = nullptr;
    static constexpr size_t kLineBufSize = 256;
    char line_buf_[kLineBufSize] = {};
    size_t line_buf_pos_ = 0;
    static constexpr size_t kResponseBufSize = 128;
    char response_buf_[kResponseBufSize] = {};
    volatile bool got_ok_ = false;
    volatile bool got_error_ = false;

    // Static instance pointer for the C callback
    static MQTTOTAHandler* active_instance_;
};
