#include "fleet_manager.hh"

#include <cctype>
#include <cstring>
#include <new>

#include "adsbee_server.hh"
#include "auto_update_manager.hh"
#include "comms.hh"
#include "esp_heap_caps.h"
#include "esp_random.h"
#include "hal.hh"
#include "hardware_capabilities.hh"
#include "object_dictionary.hh"
#include "settings.hh"

FleetManager fleet_manager;

static void fleet_task(void* pvParameters) {
    fleet_manager.Task();
    vTaskDelete(NULL);
}

void FleetManager::Stop() {
    adsbee_server.aircraft_dictionary.SetFleetRecorder(nullptr);
    xSemaphoreTake(mutex_, portMAX_DELAY);
    next_seq_ = reporter_->seq();
    delete reporter_;
    reporter_ = nullptr;
    xSemaphoreGive(mutex_);
    delete live_;
    live_ = nullptr;
    low_memory_ = false;
}

void FleetManager::Update() {
    if (task_ != nullptr) return;  // A report is being sent; it owns the pending report.
    const SettingsManager::Settings& settings = settings_manager.settings;
    uint32_t now_ms = NowMs();
    if (!settings.fleet_enabled) {
        if (reporter_ != nullptr) Stop();
        return;
    }

    if (reporter_ == nullptr) {
        char version[AutoUpdatePlatform::kVersionMaxLen + 1];
        AutoUpdateManager::RunningVersion(version, sizeof(version));
        FleetRecorder* live = new (std::nothrow) FleetRecorder();
        FleetReporter* reporter = new (std::nothrow) FleetReporter(*this, version, FleetReporter::Config(), next_seq_);
        if (live == nullptr || reporter == nullptr) {
            delete live;
            delete reporter;
            return;
        }
        live_ = live;
        reporter->Restart(*live_, now_ms);
        next_report_timestamp_ms_ = now_ms + reporter->FirstDelayMs(now_ms);
        strncpy(token_seen_, settings.fleet_token, sizeof(token_seen_) - 1);
        xSemaphoreTake(mutex_, portMAX_DELAY);
        reporter_ = reporter;
        xSemaphoreGive(mutex_);
        adsbee_server.aircraft_dictionary.SetFleetRecorder(live_);
        CONSOLE_INFO("FleetManager::Update", "Fleet reports on, to %s.", settings.fleet_server);
    }
    if (strncmp(token_seen_, settings.fleet_token, sizeof(token_seen_) - 1) != 0) {
        strncpy(token_seen_, settings.fleet_token, sizeof(token_seen_) - 1);
        reporter_->ClearStop();  // A new token undoes a 410.
    }

    // Aircraft-derived receiver positions move with the aircraft: no range map from them.
    const ObjectDictionary::RP2040DeviceStatus& rp2040 = object_dictionary.composite_device_status.rp2040;
    SettingsManager::RxPosition::PositionSource source = rp2040.rx_position.source;
    bool range_valid = rp2040.rx_position_available && SettingsManager::RxPosition::MayBeTransmittedAsOwnPosition(source);
    live_->record_range = range_valid;

    if (static_cast<int32_t>(now_ms - next_report_timestamp_ms_) < 0) return;
    if (auto_update_manager.Busy()) {
        next_report_timestamp_ms_ = now_ms + kBusyRetryMs;  // One TLS session at a time.
        return;
    }
    uint32_t free_bytes = HardwareCapabilities::GetInternalFreeBytes();
    if (free_bytes < kMinFreeHeapBytesToRun) {
        if (!low_memory_) {
            CONSOLE_WARNING("FleetManager::Update", "Not sending fleet report: %lu Bytes of heap free, need %lu.",
                            (unsigned long)free_bytes, (unsigned long)kMinFreeHeapBytesToRun);
        }
        low_memory_ = true;
        next_report_timestamp_ms_ = now_ms + kLowMemoryRetryMs;
        return;
    }
    low_memory_ = false;

    FleetReporter::DeviceState state;
    state.auto_update = settings.auto_update_enabled;
    state.rx_position_valid = rp2040.rx_position_available;
    state.latitude_deg = rp2040.rx_position.latitude_deg;
    state.longitude_deg = rp2040.rx_position.longitude_deg;
    state.altitude_m = FeetToMeters(rp2040.rx_position.FilterAltitudeFt());
    char source_str[SettingsManager::RxPosition::kPositionSourceStrMaxLen] = {0};
    if (source < SettingsManager::RxPosition::kNumPositionSources) {
        const char* s = SettingsManager::RxPosition::kPositionSourceStrs[source];
        for (size_t i = 0; s[i] && i + 1 < sizeof(source_str); i++) source_str[i] = tolower((unsigned char)s[i]);
    }
    state.rx_position_source = source_str;
    state.range_valid = range_valid;
    reporter_->TakePeriod(*live_, now_ms, state);

    strncpy(server_, settings.fleet_server, sizeof(server_) - 1);
    strncpy(token_, settings.fleet_token, sizeof(token_) - 1);
    if (xTaskCreate(fleet_task, "fleet", kTaskStackSizeBytes, NULL, kTaskPriority, &task_) != pdPASS) {
        task_ = nullptr;
        next_report_timestamp_ms_ = now_ms + kLowMemoryRetryMs;
        CONSOLE_ERROR("FleetManager::Update", "Not enough memory for the fleet report task.");
    }
}

void FleetManager::Task() {
    uint32_t start_ms = NowMs();
    uint32_t delay_ms = reporter_->Send(server_, token_);
    http_.Close();  // Hourly: not worth holding a TLS session's buffers.
    const FleetReporter::Status& status = reporter_->status();
    CONSOLE_INFO("FleetManager::Task",
                 "Report %lu: %s (HTTP %d, %u Bytes, %lu ms), next in %lu s. Stack headroom %u Bytes, lowest free heap "
                 "since boot %u Bytes.",
                 (unsigned long)status.seq, status.result, status.last_http_status, status.last_body_len,
                 (unsigned long)(NowMs() - start_ms), (unsigned long)(delay_ms / 1000),
                 (unsigned)uxTaskGetStackHighWaterMark(NULL),
                 (unsigned)heap_caps_get_minimum_free_size(HardwareCapabilities::kInternalHeapCaps));
    const FleetProfile& p = fleet_profile;
    auto avg = [&](int i) { return p.calls[i] ? (unsigned long)(p.cycles[i] / p.calls[i]) : 0ul; };
    CONSOLE_PRINTF("FLEET_PROFILE uptime_s=%lu record_calls=%lu record_avg_cyc=%lu record_total_cyc=%llu recorded=%lu "
                   "mark_calls=%lu mark_avg_cyc=%lu mark_total_cyc=%llu second_calls=%lu second_avg_cyc=%lu\r\n",
                   (unsigned long)(NowMs() / 1000), (unsigned long)p.calls[0], avg(0), (unsigned long long)p.cycles[0],
                   (unsigned long)p.recorded, (unsigned long)p.calls[1], avg(1), (unsigned long long)p.cycles[1],
                   (unsigned long)p.calls[2], avg(2));
    CONSOLE_PRINTF("FLEET_PROFILE2 update_calls=%lu update_avg_cyc=%lu update_total_cyc=%llu sizeof_recorder=%u sizeof_reporter=%u "
                   "sizeof_manager=%u body=%u free_heap=%u min_free_heap=%u stack_free=%u\r\n",
                   (unsigned long)p.calls[3], avg(3),
                   (unsigned long long)p.cycles[3], (unsigned)sizeof(FleetRecorder), (unsigned)sizeof(FleetReporter),
                   (unsigned)sizeof(FleetManager), status.last_body_len,
                   (unsigned)heap_caps_get_free_size(HardwareCapabilities::kInternalHeapCaps),
                   (unsigned)heap_caps_get_minimum_free_size(HardwareCapabilities::kInternalHeapCaps),
                   (unsigned)uxTaskGetStackHighWaterMark(NULL));
    next_report_timestamp_ms_ = NowMs() + delay_ms;
    task_ = nullptr;
}

void FleetManager::GetStatus(Status& status) {
    status = Status();
    status.enabled = settings_manager.settings.fleet_enabled;
    uint32_t now_s = NowMs() / 1000;
    xSemaphoreTake(mutex_, portMAX_DELAY);
    if (reporter_ != nullptr) {
        const FleetReporter::Status& s = reporter_->status();
        status.result = low_memory_ ? "low memory" : task_ != nullptr ? "sending" : s.stopped ? "removed" : s.result;
        status.http_status = s.last_http_status;
        status.last_report_s_ago = s.last_ok_s ? now_s - s.last_ok_s : UINT32_MAX;
        status.last_attempt_s_ago = s.last_attempt_s ? now_s - s.last_attempt_s : UINT32_MAX;
        int32_t next_ms = static_cast<int32_t>(next_report_timestamp_ms_ - NowMs());
        status.next_report_s = next_ms > 0 ? next_ms / 1000 : 0;
        status.seq = s.seq;
        status.body_len = s.last_body_len;
    }
    xSemaphoreGive(mutex_);
}

uint32_t FleetManager::NowMs() { return get_time_since_boot_ms(); }

uint32_t FleetManager::Random() { return esp_random(); }

bool FleetManager::Online() { return comms_manager.HasIP(); }

bool FleetManager::GetIdentity(AutoUpdatePlatform::Identity& identity) {
    if (auto_update_manager.Busy()) return false;  // It uses the same RP2040 request.
    bool ok = auto_update_manager.GetIdentity(identity);
    // Keep the OTA keys only as long as the report needs them (the updater keeps its own copy).
    object_dictionary.device_identity_valid = false;
    memset(&object_dictionary.device_identity, 0, sizeof(object_dictionary.device_identity));
    return ok;
}

bool FleetManager::Http(const AutoUpdatePlatform::HttpRequest& request, AutoUpdatePlatform::HttpResult& result,
                        AutoUpdatePlatform::BodySink* sink) {
    return http_.Request(request.path, request, result, sink);
}

void FleetManager::SetFirmwareTarget(const char* tag, const char* channel) {
    auto_update_manager.SetFleetTarget(tag);
}
