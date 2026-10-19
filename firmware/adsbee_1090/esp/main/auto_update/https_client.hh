#pragma once

#include "auto_updater.hh"
#include "esp_http_client.h"

/**
 * esp_http_client wrapper for the automatic updater and fleet reports: one kept-alive connection, the response body
 * streamed to a BodySink, server certificates checked against the built-in CA bundle. http:// URLs work too.
 */
class HttpsClient {
   public:
    static constexpr uint32_t kTimeoutMs = 15000;
    static constexpr uint16_t kBufferLenBytes = 1024;

    // One exchange with url. False means no response (DNS, TCP, TLS, timeout or an aborted body).
    bool Request(const char* url, const AutoUpdatePlatform::HttpRequest& request, AutoUpdatePlatform::HttpResult& result,
                 AutoUpdatePlatform::BodySink* sink);

    // Ends the connection and frees its buffers.
    void Close();

   private:
    static esp_err_t EventHandler(esp_http_client_event_t* event);
    bool Perform(const char* url, const AutoUpdatePlatform::HttpRequest& request, AutoUpdatePlatform::BodySink* sink);

    esp_http_client_handle_t client_ = nullptr;
    AutoUpdatePlatform::BodySink* sink_ = nullptr;
    bool aborted_ = false;
    bool got_body_ = false;
    uint32_t retry_after_s_ = 0;
};
