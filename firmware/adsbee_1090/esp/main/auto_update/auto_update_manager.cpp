#include "auto_update_manager.hh"

#include <cstring>
#include <new>

#include "comms.hh"
#include "device_info.hh"
#include "esp_crt_bundle.h"
#include "esp_random.h"
#include "hal.hh"
#include "nvs.h"
#include "object_dictionary.hh"
#include "settings.hh"

#ifndef AUTO_UPDATE_API_BASE
#define AUTO_UPDATE_API_BASE "https://adsbee.aero/api/fw/v1/"
#endif
const char AutoUpdateManager::kAPIBase[] = AUTO_UPDATE_API_BASE;

#ifdef AUTO_UPDATE_TEST_CA
// Bench builds only: trust this CA instead of the certificate bundle (see CMakeLists.txt).
extern const char auto_update_test_ca_pem_start[] asm("_binary_auto_update_test_ca_pem_start");
#endif

static const char kNVSNamespace[] = "auto_update";
static const char kNVSStateKey[] = "state";

AutoUpdateManager auto_update_manager;

static void auto_update_task(void* pvParameters) {
    auto_update_manager.Task();  // Returns when the setting is turned off.
    vTaskDelete(NULL);
}

void AutoUpdateManager::Update() {
    if (task_ != nullptr || !Enabled()) return;
    if (console_rx_buf_ == nullptr) {
        console_rx_buf_ = xStreamBufferCreate(kConsoleRxBufLenBytes, 1);
        if (console_rx_buf_ == nullptr) return;
    }
    if (xTaskCreate(auto_update_task, "auto_update", kTaskStackSizeBytes, NULL, kTaskPriority, &task_) != pdPASS) {
        task_ = nullptr;
        CONSOLE_ERROR("AutoUpdateManager::Update", "Not enough memory for the automatic update task.");
    }
}

void AutoUpdateManager::Task() {
    char version[kVersionMaxLen + 1];
    if (ObjectDictionary::kFirmwareVersionReleaseCandidate == 0) {
        snprintf(version, sizeof(version), "%d.%d.%d", ObjectDictionary::kFirmwareVersionMajor,
                 ObjectDictionary::kFirmwareVersionMinor, ObjectDictionary::kFirmwareVersionPatch);
    } else {
        snprintf(version, sizeof(version), "%d.%d.%d-rc%d", ObjectDictionary::kFirmwareVersionMajor,
                 ObjectDictionary::kFirmwareVersionMinor, ObjectDictionary::kFirmwareVersionPatch,
                 ObjectDictionary::kFirmwareVersionReleaseCandidate);
    }
    AutoUpdater::Config config;
#ifdef AUTO_UPDATE_FIRST_CHECK_S
    config.first_check_delay_ms = AUTO_UPDATE_FIRST_CHECK_S * 1000;  // Bench builds only.
    config.first_check_jitter_ms = 0;
#endif
    AutoUpdater* updater = new (std::nothrow) AutoUpdater(*this, version, config);
    if (updater != nullptr) {
        xSemaphoreTake(updater_mutex_, portMAX_DELAY);
        updater_ = updater;
        xSemaphoreGive(updater_mutex_);
        CONSOLE_INFO("AutoUpdateManager::Task", "Automatic updates on, running %s.", version);

        uint32_t delay_ms = updater->FirstDelayMs(NowMs());
        while (Enabled()) {
            uint32_t start_ms = NowMs();
            while (Enabled() && NowMs() - start_ms < delay_ms) {
                vTaskDelay(pdMS_TO_TICKS(1000));
            }
            if (!Enabled()) break;
            xStreamBufferReset(console_rx_buf_);
            capturing_ = true;
            delay_ms = updater->RunOnce();
            capturing_ = false;
            HTTPClose();  // TLS buffers are only held while talking to the service.
            if (updater->state() == AutoUpdater::kFailed) {
                CONSOLE_WARNING("AutoUpdateManager::Task", "Update to %s failed: %s.", updater->version(),
                                updater->detail());
            }
            CONSOLE_INFO("AutoUpdateManager::Task", "State %s, next check in %lu s, stack headroom %u Bytes.",
                         AutoUpdater::StateToStr(updater->state()), (unsigned long)(delay_ms / 1000),
                         (unsigned)uxTaskGetStackHighWaterMark(NULL));
        }

        xSemaphoreTake(updater_mutex_, portMAX_DELAY);
        updater_ = nullptr;
        xSemaphoreGive(updater_mutex_);
        delete updater;
    }
    HTTPClose();
    // The OTA keys are only needed while the feature is on.
    object_dictionary.device_identity_valid = false;
    memset(&object_dictionary.device_identity, 0, sizeof(object_dictionary.device_identity));
    task_ = nullptr;
}

void AutoUpdateManager::GetStatus(Status& status) {
    status = Status();
    status.enabled = Enabled();
    xSemaphoreTake(updater_mutex_, portMAX_DELAY);
    if (updater_ != nullptr) {
        status.state = updater_->state();
        strncpy(status.version, updater_->version(), kVersionMaxLen);
        status.progress_percent = updater_->progress_percent();
    }
    xSemaphoreGive(updater_mutex_);
}

void AutoUpdateManager::NoteUserOTA(const char* buf, size_t len, const char* marker) {
    size_t marker_len = strlen(marker);
    for (size_t i = 0; i + marker_len <= len; i++) {
        if (buf[i] == marker[0] && memcmp(buf + i, marker, marker_len) == 0) {
            last_user_ota_timestamp_ms_ = get_time_since_boot_ms();
            user_ota_seen_ = true;
            return;
        }
    }
}

void AutoUpdateManager::OnConsoleOutput(const uint8_t* buf, size_t len) {
    if (capturing_) {
        if (console_rx_buf_) xStreamBufferSend(console_rx_buf_, buf, len, 0);
    } else if (task_ != nullptr) {
        // An OTA driven from USB or the web shows up as the RP2040's replies to its writes.
        NoteUserOTA(reinterpret_cast<const char*>(buf), len, "Bytes to partition");
    }
}

void AutoUpdateManager::OnConsoleInput(const char* buf, size_t len) {
    if (task_ != nullptr) NoteUserOTA(buf, len, "AT+OTA=");
}

uint32_t AutoUpdateManager::NowMs() { return get_time_since_boot_ms(); }

void AutoUpdateManager::SleepMs(uint32_t ms) { vTaskDelay(pdMS_TO_TICKS(ms)); }

uint32_t AutoUpdateManager::Random() { return esp_random(); }

bool AutoUpdateManager::Enabled() { return settings_manager.settings.auto_update_enabled; }

bool AutoUpdateManager::Online() { return comms_manager.HasIP(); }

bool AutoUpdateManager::GetIdentity(Identity& identity) {
    object_dictionary.device_identity_valid = false;
    if (!object_dictionary.RequestSCCommand(ObjectDictionary::SCCommandRequest{
            .command = ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck,
            .addr = ObjectDictionary::Address::kAddrDeviceIdentity,
            .offset = 0,
            .len = sizeof(SettingsManager::DeviceIdentity)})) {
        return false;
    }
    uint32_t start_ms = NowMs();
    while (!object_dictionary.device_identity_valid) {
        if (NowMs() - start_ms > kIdentityTimeoutMs) {
            CONSOLE_ERROR("AutoUpdateManager::GetIdentity", "No device identity from the RP2040.");
            return false;
        }
        vTaskDelay(pdMS_TO_TICKS(50));
    }
    const SettingsManager::DeviceIdentity& id = object_dictionary.device_identity;
    snprintf(identity.unique_id, sizeof(identity.unique_id), "%02X%02X%02X%02X%02X%02X%02X%02X", id.unique_id[0],
             id.unique_id[1], id.unique_id[2], id.unique_id[3], id.unique_id[4], id.unique_id[5], id.unique_id[6],
             id.unique_id[7]);
    ObjectDictionary::ESP32DeviceInfo esp32_info = GetESP32DeviceInfo();
    snprintf(identity.mac_address, sizeof(identity.mac_address), "%02X:%02X:%02X:%02X:%02X:%02X",
             esp32_info.base_mac[0], esp32_info.base_mac[1], esp32_info.base_mac[2], esp32_info.base_mac[3],
             esp32_info.base_mac[4], esp32_info.base_mac[5]);
    strncpy(identity.part_code, id.part_code, sizeof(identity.part_code) - 1);
    for (uint16_t i = 0; i < SettingsManager::DeviceInfo::kNumOTAKeys; i++) {
        strncpy(identity.ota_keys[i], id.ota_keys[i], sizeof(identity.ota_keys[i]) - 1);
    }
    return true;
}

esp_err_t AutoUpdateManager::HTTPEventHandler(esp_http_client_event_t* event) {
    AutoUpdateManager* self = static_cast<AutoUpdateManager*>(event->user_data);
    switch (event->event_id) {
        case HTTP_EVENT_ON_HEADER:
            if (strcasecmp(event->header_key, "Retry-After") == 0) {
                self->retry_after_s_ = strtoul(event->header_value, nullptr, 10);
            }
            break;
        case HTTP_EVENT_ON_DATA:
            if (self->sink_ != nullptr && !self->aborted_ &&
                !self->sink_->OnBody(esp_http_client_get_status_code(event->client),
                                     static_cast<const uint8_t*>(event->data), event->data_len)) {
                self->aborted_ = true;  // Ranges are small: the rest of this one is read and dropped.
            }
            break;
        default:
            break;
    }
    return ESP_OK;
}

void AutoUpdateManager::HTTPClose() {
    if (client_ != nullptr) {
        esp_http_client_cleanup(client_);
        client_ = nullptr;
    }
}

bool AutoUpdateManager::Http(const HttpRequest& request, HttpResult& result, BodySink* sink) {
    char url[sizeof(kAPIBase) + 160];
    snprintf(url, sizeof(url), "%s%s", kAPIBase, request.path);
    if (client_ == nullptr) {
        esp_http_client_config_t config = {};
        config.url = url;
        config.timeout_ms = kHTTPTimeoutMs;
        config.event_handler = HTTPEventHandler;
        config.user_data = this;
        config.buffer_size = kHTTPBufferLenBytes;
        config.buffer_size_tx = kHTTPBufferLenBytes;
        config.keep_alive_enable = true;
        config.user_agent = "ADSBee1090";
#ifdef AUTO_UPDATE_TEST_CA
        config.cert_pem = auto_update_test_ca_pem_start;
        config.skip_cert_common_name_check = true;
#else
        config.crt_bundle_attach = esp_crt_bundle_attach;
#endif
        client_ = esp_http_client_init(&config);
        if (client_ == nullptr) return false;
    } else {
        esp_http_client_set_url(client_, url);
    }

    esp_http_client_set_method(client_, strcmp(request.method, "POST") == 0 ? HTTP_METHOD_POST : HTTP_METHOD_GET);
    char header[AutoUpdater::kTokenMaxLen + 16];
    if (request.token != nullptr) {
        snprintf(header, sizeof(header), "Bearer %s", request.token);
        esp_http_client_set_header(client_, "Authorization", header);
    } else {
        esp_http_client_delete_header(client_, "Authorization");
    }
    if (request.range_first >= 0) {
        snprintf(header, sizeof(header), "bytes=%ld-%ld", (long)request.range_first, (long)request.range_last);
        esp_http_client_set_header(client_, "Range", header);
    } else {
        esp_http_client_delete_header(client_, "Range");
    }
    if (request.body != nullptr) {
        esp_http_client_set_header(client_, "Content-Type", "application/json");
        esp_http_client_set_post_field(client_, request.body, strlen(request.body));
    } else {
        esp_http_client_delete_header(client_, "Content-Type");
        esp_http_client_set_post_field(client_, nullptr, 0);
    }

    sink_ = sink;
    aborted_ = false;
    retry_after_s_ = 0;
    esp_err_t err = esp_http_client_perform(client_);
    sink_ = nullptr;
    if (err != ESP_OK || aborted_) {
        HTTPClose();  // Start the next request on a fresh connection.
        return false;
    }
    result.status = esp_http_client_get_status_code(client_);
    result.retry_after_s = retry_after_s_;
    return true;
}

void AutoUpdateManager::ConsoleSend(const uint8_t* data, size_t len) {
    // Same queue the /console websocket feeds; the RP2040 pulls from it over SPI.
    static constexpr uint32_t kTimeoutMs = 10000;
    uint32_t start_ms = NowMs();
    size_t sent = 0;
    while (sent < len && NowMs() - start_ms < kTimeoutMs) {
        xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);
        // All or nothing, so a payload is never interleaved with a web client's typing.
        bool fits = static_cast<size_t>(object_dictionary.network_console_rx_queue.MaxNumElements() -
                                        object_dictionary.network_console_rx_queue.Length()) >= len;
        while (fits && sent < len &&
               object_dictionary.network_console_rx_queue.Enqueue(static_cast<char>(data[sent]))) {
            sent++;
        }
        xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
        if (sent < len) vTaskDelay(pdMS_TO_TICKS(20));
    }
}

bool AutoUpdateManager::ConsoleReadLine(char* line, size_t line_size, uint32_t timeout_ms) {
    uint32_t start_ms = NowMs();
    size_t len = 0;
    for (;;) {
        uint32_t elapsed_ms = NowMs() - start_ms;
        if (elapsed_ms >= timeout_ms) return false;
        char c;
        if (xStreamBufferReceive(console_rx_buf_, &c, 1, pdMS_TO_TICKS(timeout_ms - elapsed_ms)) != 1) {
            return false;
        }
        if (c == '\n') {
            line[len] = '\0';
            return true;
        }
        if (len + 1 < line_size) line[len++] = c;  // Longer lines are cut.
    }
}

const char* AutoUpdateManager::ConsoleReportingProtocol() {
    SettingsManager::ReportingProtocol protocol =
        settings_manager.settings.reporting_protocols[SettingsManager::SerialInterface::kConsole];
    if (protocol == SettingsManager::ReportingProtocol::kNoReports ||
        protocol >= SettingsManager::ReportingProtocol::kNumProtocols) {
        return nullptr;
    }
    return SettingsManager::kReportingProtocolStrs[protocol];
}

bool AutoUpdateManager::UserOTAActive() {
    return user_ota_seen_ && NowMs() - last_user_ota_timestamp_ms_ < kUserOTAHoldoffMs;
}

void AutoUpdateManager::LoadState(SavedState& state) {
    state = SavedState();
    nvs_handle_t handle;
    if (nvs_open(kNVSNamespace, NVS_READONLY, &handle) != ESP_OK) return;
    SavedState stored;
    size_t len = sizeof(stored);
    if (nvs_get_blob(handle, kNVSStateKey, &stored, &len) == ESP_OK && len == sizeof(stored)) {
        state = stored;
    }
    nvs_close(handle);
}

void AutoUpdateManager::SaveState(const SavedState& state) {
    nvs_handle_t handle;
    if (nvs_open(kNVSNamespace, NVS_READWRITE, &handle) != ESP_OK) return;
    if (nvs_set_blob(handle, kNVSStateKey, &state, sizeof(state)) == ESP_OK) nvs_commit(handle);
    nvs_close(handle);
}
