#pragma once

#include "fleet_reporter.hh"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#include "https_client.hh"
#include "settings.hh"

/**
 * Runs FleetReporter (common/fleet) on the ESP32 for AT+FLEET: the live range map fed by the aircraft dictionary, and a
 * task per report for the HTTPS request. With the setting off nothing is allocated.
 */
class FleetManager : public FleetPlatform {
   public:
    static constexpr uint32_t kTaskStackSizeBytes = 8192;  // Internal SRAM; the TLS handshake is the deep part.
    static constexpr UBaseType_t kTaskPriority = tskIDLE_PRIORITY;
    // Free internal heap needed to start a report: about 40 kB peak with TLS, plus what the network stacks need.
    static constexpr uint32_t kMinFreeHeapBytesToRun = 56 * 1024;
    static constexpr uint32_t kBusyRetryMs = 30 * 1000;  // While an automatic update runs.
    static constexpr uint32_t kLowMemoryRetryMs = 10 * 60 * 1000;

    struct Status {
        bool enabled = false;
        const char* result = "off";
        int http_status = 0;
        uint32_t last_report_s_ago = 0;  // UINT32_MAX: none yet.
        uint32_t last_attempt_s_ago = 0;
        uint32_t next_report_s = 0;
        uint32_t seq = 0;
        uint16_t body_len = 0;
    };

    /**
     * Ends periods and starts reports when due. Call from the task that updates the aircraft dictionary.
     */
    void Update();

    void GetStatus(Status& status);

    // A report is being sent.
    bool Busy() const { return task_ != nullptr; }

    void Task();

    // FleetPlatform
    uint32_t NowMs() override;
    uint32_t Random() override;
    bool Online() override;
    bool GetIdentity(AutoUpdatePlatform::Identity& identity) override;
    bool Http(const AutoUpdatePlatform::HttpRequest& request, AutoUpdatePlatform::HttpResult& result,
              AutoUpdatePlatform::BodySink* sink) override;
    void SetFirmwareTarget(const char* tag, const char* channel) override;

   private:
    void Stop();

    TaskHandle_t task_ = nullptr;
    SemaphoreHandle_t mutex_ = xSemaphoreCreateMutex();  // Guards reporter_ against GetStatus().
    FleetRecorder* live_ = nullptr;
    FleetReporter* reporter_ = nullptr;
    uint32_t next_seq_ = 0;  // Survives turning the setting off and on.
    uint32_t next_report_timestamp_ms_ = 0;
    bool low_memory_ = false;
    char token_seen_[SettingsManager::Settings::kFleetTokenMaxLen + 1] = {0};
    // The task's copies of the settings, which may change while it runs.
    char server_[SettingsManager::Settings::kFleetServerMaxLen + 1] = {0};
    char token_[SettingsManager::Settings::kFleetTokenMaxLen + 1] = {0};
    HttpsClient http_;
};

extern FleetManager fleet_manager;
