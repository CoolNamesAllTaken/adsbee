#pragma once

#include "auto_updater.hh"
#include "esp_http_client.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/stream_buffer.h"
#include "freertos/task.h"

/**
 * Runs AutoUpdater (common/auto_update) on the ESP32: a task that exists only while the AUTO_UPDATE setting is on,
 * HTTPS to the firmware service, the RP2040 console through the network console queues, and state in NVS.
 */
class AutoUpdateManager : public AutoUpdatePlatform {
   public:
    // The firmware service. A bench build can point somewhere else: idf.py -DAUTO_UPDATE_API_BASE=http://host/api/fw/v1/
    static const char kAPIBase[];

    // Task stack is internal SRAM. The TLS handshake is the deep part.
    static constexpr uint32_t kTaskStackSizeBytes = 8192;
    static constexpr UBaseType_t kTaskPriority = tskIDLE_PRIORITY;  // Same as the feed task: never ahead of SPI or feeds.
    static constexpr uint32_t kHTTPTimeoutMs = 15000;
    static constexpr uint16_t kHTTPBufferLenBytes = 1024;
    static constexpr uint16_t kConsoleRxBufLenBytes = 2048;  // A burst of RP2040 log lines must not push out an OK.
    static constexpr uint32_t kIdentityTimeoutMs = 5000;
    // A manual AT+OTA seen this recently means an update is in progress.
    static constexpr uint32_t kUserOTAHoldoffMs = 10 * 60 * 1000;

    struct Status {
        bool enabled = false;
        AutoUpdater::State state = AutoUpdater::kIdle;
        char version[kVersionMaxLen + 1] = {0};
        uint8_t progress_percent = 0;
    };

    /**
     * Starts the task when the setting is on. Call from the main loop.
     */
    void Update();

    /**
     * Console bytes from the RP2040. Called from the SPI receive task: never blocks.
     */
    void OnConsoleOutput(const uint8_t* buf, size_t len);

    /**
     * Console bytes a /console client sent to the RP2040.
     */
    void OnConsoleInput(const char* buf, size_t len);

    void GetStatus(Status& status);

    void Task();

    // AutoUpdatePlatform
    uint32_t NowMs() override;
    void SleepMs(uint32_t ms) override;
    uint32_t Random() override;
    bool Enabled() override;
    bool Online() override;
    bool GetIdentity(Identity& identity) override;
    bool Http(const HttpRequest& request, HttpResult& result, BodySink* sink) override;
    void ConsoleSend(const uint8_t* data, size_t len) override;
    bool ConsoleReadLine(char* line, size_t line_size, uint32_t timeout_ms) override;
    const char* ConsoleReportingProtocol() override;
    bool UserOTAActive() override;
    void LoadState(SavedState& state) override;
    void SaveState(const SavedState& state) override;

   private:
    static esp_err_t HTTPEventHandler(esp_http_client_event_t* event);
    bool HTTPPerform(const HttpRequest& request, BodySink* sink);
    void HTTPClose();
    void NoteUserOTA(const char* buf, size_t len, const char* marker);

    TaskHandle_t task_ = nullptr;
    SemaphoreHandle_t updater_mutex_ = xSemaphoreCreateMutex();
    AutoUpdater* updater_ = nullptr;

    esp_http_client_handle_t client_ = nullptr;
    BodySink* sink_ = nullptr;
    bool aborted_ = false;
    bool got_body_ = false;
    uint32_t retry_after_s_ = 0;

    StreamBufferHandle_t console_rx_buf_ = nullptr;
    volatile bool capturing_ = false;  // The updater is reading the console.
    volatile uint32_t last_user_ota_timestamp_ms_ = 0;
    volatile bool user_ota_seen_ = false;
};

extern AutoUpdateManager auto_update_manager;
