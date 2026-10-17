#include "network_time.hh"

#include <sys/time.h>

#include <cstring>

#include "comms.hh"
#include "esp_netif_sntp.h"
#include "hal.hh"

NetworkTime network_time;

void NetworkTime::OnSync(struct timeval* tv) {
    network_time.last_sync_timestamp_ms_ = get_time_since_boot_ms();
    network_time.synced_ = true;
}

void NetworkTime::Start() {
    strncpy(server_, settings_manager.settings.ntp_server, sizeof(server_) - 1);
    server_[sizeof(server_) - 1] = '\0';
    esp_sntp_config_t config = ESP_NETIF_SNTP_DEFAULT_CONFIG(server_);
    config.sync_cb = OnSync;
    config.start = comms_manager.HasIP();
    had_ip_ = config.start;
    esp_err_t err = esp_netif_sntp_init(&config);
    if (err != ESP_OK) {
        CONSOLE_ERROR("NetworkTime::Start", "Failed to start SNTP with server %s: %s.", server_, esp_err_to_name(err));
        return;
    }
    running_ = true;
    CONSOLE_INFO("NetworkTime::Start", "SNTP started with server %s.", server_);
}

void NetworkTime::Stop() {
    esp_netif_sntp_deinit();
    running_ = false;
    synced_ = false;
    CONSOLE_INFO("NetworkTime::Stop", "SNTP stopped.");
}

void NetworkTime::Update() {
    const SettingsManager::Settings& settings = settings_manager.settings;
    bool wanted = SettingsManager::ProtocolInUse(settings, SettingsManager::kASTERIX) && settings.ntp_server[0] != '\0';
    if (running_ && (!wanted || strncmp(server_, settings.ntp_server, sizeof(server_)) != 0)) {
        Stop();
    }
    if (!running_) {
        if (wanted) Start();
        return;
    }
    // Ask right away once a network is up, instead of waiting for the next retry.
    bool has_ip = comms_manager.HasIP();
    if (has_ip && !had_ip_) {
        esp_netif_sntp_start();
    }
    had_ip_ = has_ip;
}

bool NetworkTime::GetUTC(uint32_t& utc_ms_of_day, uint32_t& local_ms) {
    if (!running_ || !synced_ || get_time_since_boot_ms() - last_sync_timestamp_ms_ > kMaxSyncAgeMs) {
        return false;
    }
    struct timeval tv;
    gettimeofday(&tv, nullptr);
    local_ms = get_time_since_boot_ms();
    utc_ms_of_day = static_cast<uint32_t>((tv.tv_sec % 86400) * 1000 + tv.tv_usec / 1000);
    return true;
}

void NetworkTime::GetStatus(Status& status) {
    status.enabled = running_;
    uint32_t utc_ms_of_day, local_ms;
    status.synced = GetUTC(utc_ms_of_day, local_ms);
    status.last_sync_age_s = synced_ ? (get_time_since_boot_ms() - last_sync_timestamp_ms_) / 1000 : 0;
    status.server = running_ ? server_ : "";
}
