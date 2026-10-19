#include "https_client.hh"

#include <cstring>

#include "esp_crt_bundle.h"

#ifdef AUTO_UPDATE_TEST_CA
// Bench builds only: trust this CA instead of the certificate bundle (see CMakeLists.txt).
extern const char auto_update_test_ca_pem_start[] asm("_binary_auto_update_test_ca_pem_start");
#endif

esp_err_t HttpsClient::EventHandler(esp_http_client_event_t* event) {
    HttpsClient* self = static_cast<HttpsClient*>(event->user_data);
    switch (event->event_id) {
        case HTTP_EVENT_ON_HEADER:
            if (strcasecmp(event->header_key, "Retry-After") == 0) {
                self->retry_after_s_ = strtoul(event->header_value, nullptr, 10);
            }
            break;
        case HTTP_EVENT_ON_DATA:
            self->got_body_ = true;
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

void HttpsClient::Close() {
    if (client_ != nullptr) {
        esp_http_client_cleanup(client_);
        client_ = nullptr;
    }
}

bool HttpsClient::Request(const char* url, const AutoUpdatePlatform::HttpRequest& request,
                          AutoUpdatePlatform::HttpResult& result, AutoUpdatePlatform::BodySink* sink) {
    // A kept-alive connection the server has closed in the meantime fails at once: try again on a fresh one.
    for (int attempt = 0; attempt < 2; attempt++) {
        bool reused = client_ != nullptr;
        if (Perform(url, request, sink)) {
            result.status = esp_http_client_get_status_code(client_);
            result.retry_after_s = retry_after_s_;
            return true;
        }
        Close();
        if (!reused || got_body_ || aborted_) break;
    }
    return false;
}

bool HttpsClient::Perform(const char* url, const AutoUpdatePlatform::HttpRequest& request,
                          AutoUpdatePlatform::BodySink* sink) {
    if (client_ == nullptr) {
        esp_http_client_config_t config = {};
        config.url = url;
        config.timeout_ms = kTimeoutMs;
        config.event_handler = EventHandler;
        config.user_data = this;
        config.buffer_size = kBufferLenBytes;
        config.buffer_size_tx = kBufferLenBytes;
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
    got_body_ = false;
    retry_after_s_ = 0;
    esp_err_t err = esp_http_client_perform(client_);
    sink_ = nullptr;
    return err == ESP_OK && !aborted_;
}
