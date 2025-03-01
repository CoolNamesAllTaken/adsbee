#include "websocket_server.hh"

#include "comms.hh"
#include "hal.hh"

/**
 * This helper function digs out the WebSocketServer stored in the user context of an HTTP request in order to allow the
 * Handler() function of the proper WebSocketServer to be called.
 */
esp_err_t ws_handler(httpd_req_t *req) {
    WebSocketServer *instance = static_cast<WebSocketServer *>(req->user_ctx);
    if (instance) {
        return instance->Handler(req);
    }
    return ESP_FAIL;
}

bool WebSocketServer::Init() {
    if (!config_.message_received_callback) {
        CONSOLE_WARNING("WebSocketServer::Init",
                        "[%s] Message received callback is nullptr, WebSocketServer will probably do nothing.",
                        config_.label);
    }

    // Network console Websocket handler
    httpd_uri_t console_ws = {.uri = config_.uri,
                              .method = HTTP_GET,
                              // Pass in instance as user context to allow use of member functions in callbacks.
                              .handler = ws_handler,
                              .user_ctx = this,
                              .is_websocket = true,
                              .handle_ws_control_frames = false};
    httpd_register_uri_handler(config_.server, &console_ws);

    return true;
}

bool WebSocketServer::Update() {
    // Prune inactive network console clients.
    uint32_t timestamp_ms = get_time_since_boot_ms();  // Refresh timestamp to avoid negative values for time since last
                                                       // message (except for wraps)
    for (uint16_t i = 0; i < config_.num_clients_allowed; i++) {
        uint32_t time_since_last_message_ms = timestamp_ms - clients_[i].last_message_timestamp_ms;
        if (clients_[i].in_use && time_since_last_message_ms > config_.inactivity_timeout_ms) {
            // Client is in use and has timed out.
            int client_fd = clients_[i].client_fd;
            CONSOLE_WARNING("ADSBeeServer::Update", "[%s] Network console client %d with fd %d timed out after %lu ms.",
                            config_.label, i, client_fd, time_since_last_message_ms);
            RemoveClient(client_fd);
        }
    }
    return true;
}

esp_err_t WebSocketServer::Handler(httpd_req_t *req) {
    int client_fd = httpd_req_to_sockfd(req);

    // Check if this client_fd is already connected
    for (int i = 0; i < config_.num_clients_allowed; i++) {
        if (clients_[i].in_use && clients_[i].client_fd == client_fd) {
            CONSOLE_WARNING("WebSocketServer::Handler",
                            "[%s] Client fd %d is already connected to client %d. Original connection will be removed.",
                            config_.label, client_fd, i);
            RemoveClient(client_fd);
        }
    }

    if (req->method == HTTP_GET) {
        CONSOLE_INFO("WebSocketServer::Handler", " [%s] Handshake done, new connection was opened.", config_.label);
        if (!AddClient(client_fd)) {
            CONSOLE_ERROR("WebSocketServer::Handler", "[%s] Rejecting websocket connection.", config_.label);
            // Send a close frame
            httpd_ws_frame_t ws_pkt = {
                .final = true, .fragmented = false, .type = HTTPD_WS_TYPE_CLOSE, .payload = NULL, .len = 0};

            httpd_ws_send_frame(req, &ws_pkt);

            // Return error to reject the connection
            return ESP_FAIL;
        }
        if (config_.post_connect_callback) {
            config_.post_connect_callback(this, client_fd);
        }

        return ESP_OK;
    }
    httpd_ws_frame_t ws_pkt;
    uint8_t *buf = NULL;
    memset(&ws_pkt, 0, sizeof(httpd_ws_frame_t));
    ws_pkt.type = config_.send_as_binary ? HTTPD_WS_TYPE_BINARY : HTTPD_WS_TYPE_TEXT;
    /* Set max_len = 0 to get the frame len */
    esp_err_t ret = httpd_ws_recv_frame(req, &ws_pkt, 0);
    if (ret != ESP_OK) {
        CONSOLE_ERROR("WebSocketServer::Handler", "[%s] httpd_ws_recv_frame failed to get frame len with %d.",
                      config_.label, ret);
        return ret;
    }
    CONSOLE_INFO("WebSocketServer::Handler", "[%s] frame len is %d.", config_.label, ws_pkt.len);
    if (ws_pkt.len) {
        /* ws_pkt.len + 1 is for NULL termination as we are expecting a string */
        buf = (uint8_t *)calloc(1, ws_pkt.len + 1);
        if (buf == NULL) {
            CONSOLE_ERROR("WebSocketServer::Handler", "[%s] Failed to calloc memory for buf.", config_.label);
            return ESP_ERR_NO_MEM;
        }
        ws_pkt.payload = buf;
        /* Set max_len = ws_pkt.len to get the frame payload */
        ret = httpd_ws_recv_frame(req, &ws_pkt, ws_pkt.len);
        if (ret != ESP_OK) {
            CONSOLE_ERROR("WebSocketServer::Handler", "[%s] httpd_ws_recv_frame failed with %d.", config_.label, ret);
            free(buf);
            if (config_.pre_disconnect_callback) {
                config_.pre_disconnect_callback(this, client_fd);
            }
            RemoveClient(client_fd);
            return ret;
        }

        UpdateActivityTimer(client_fd);
        // Don't print packet payload, it's not safe if it's binary data that isn't null-terminated.
        // CONSOLE_INFO("WebSocketServer::Handler", "[%s] Got packet with message: %s", config_.label, ws_pkt.payload);
        if (config_.message_received_callback) {
            config_.message_received_callback(this, client_fd, ws_pkt);
        }
    }

    free(buf);
    return ret;
}

bool WebSocketServer::AddClient(int client_fd) {
    for (int i = 0; i < config_.num_clients_allowed; i++) {
        if (!clients_[i].in_use) {
            clients_[i].in_use = true;
            clients_[i].client_fd = client_fd;
            clients_[i].last_message_timestamp_ms = get_time_since_boot_ms();
            CONSOLE_INFO("WebSocketServer::AddClient", "[%s] New client stored at index %d.", config_.label, i);
            return true;
        }
    }
    CONSOLE_ERROR("WebSocketServer::AddClient", "[%s] Can't connect additional clients, already reached maximum of %d.",
                  config_.label, config_.num_clients_allowed);
    return false;
}

bool WebSocketServer::RemoveClient(int client_fd) {
    for (int i = 0; i < config_.num_clients_allowed; i++) {
        if (clients_[i].in_use && clients_[i].client_fd == client_fd) {
            clients_[i].in_use = false;
            CONSOLE_INFO("WebSocketServer::RemoveClient", "[%s] Client %d with fd %d removed.", config_.label, i,
                         client_fd);
            clients_[i].client_fd = -1;
            return true;
        }
    }
    CONSOLE_WARNING("WebSocketServer::RemoveClient",
                    "[%s] Client with fd %d not found; it may have already been removed.", config_.label, client_fd);
    return false;
}

void WebSocketServer::BroadcastMessage(const char *message, int16_t len_bytes) {
    for (int i = 0; i < config_.num_clients_allowed; i++) {
        if (clients_[i].in_use) {
            esp_err_t ret = SendMessage(clients_[i].client_fd, message, len_bytes);
            if (ret != ESP_OK) {
                CONSOLE_ERROR("WebSocketServer::BroadcastMessage",
                              "[%s] Failed to send message to client %d due to error %s.", config_.label, i,
                              esp_err_to_name(ret));
                // If send failed, assume client disconnected
                RemoveClient(clients_[i].client_fd);
            }
        }
    }
}

esp_err_t WebSocketServer::SendMessage(int client_fd, const char *message, int16_t len_bytes) {
    httpd_ws_frame_t ws_pkt = {.final = true,
                               .fragmented = false,
                               .type = config_.send_as_binary ? HTTPD_WS_TYPE_BINARY : HTTPD_WS_TYPE_TEXT,
                               .payload = (uint8_t *)message,
                               .len = len_bytes > 0 ? len_bytes : strlen(message)};

    return httpd_ws_send_frame_async(config_.server, client_fd, &ws_pkt);
}

bool WebSocketServer::UpdateActivityTimer(int client_fd) {
    for (int i = 0; i < config_.num_clients_allowed; i++) {
        if (clients_[i].client_fd == client_fd) {
            clients_[i].last_message_timestamp_ms = get_time_since_boot_ms();
            return true;
        }
    }
    return false;  // Couldn't find client.
}