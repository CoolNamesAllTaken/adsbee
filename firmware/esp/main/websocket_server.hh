#ifndef WEBSOCKET_MANAGER_HH_
#define WEBSOCKET_MANAGER_HH_

#include <functional>

#include "esp_http_server.h"

class WebSocketServer {
   public:
    static const uint16_t kWebSocketLabelMaxLen =
        100;  // Number of chars available for label used in WebSocketManager error messages.
    static const uint16_t kMaxNumClients =
        20;  // For sizing arrays etc. See config_.num_clients_allowed for settable limit.
    static const uint16_t kURIMaxLen = 200;

    struct WebSocketManagerConfig {
        char label[kWebSocketLabelMaxLen] = "Untitled";
        httpd_handle_t server;
        char uri[kURIMaxLen] = "/your-websocket-uri";
        uint16_t num_clients_allowed = 3;
        // Time without a message before a network console client is disconnected.
        uint32_t inactivity_timeout_ms = 10 * 60e3;
        // Callback function that gets executed when the websocket connects.
        std::function<void(WebSocketServer *ws_server, int client_fd)> post_connect_callback = nullptr;
        // Callback function that gets executed when the websocket disconnects.
        std::function<void(WebSocketServer *ws_server, int client_fd)> pre_disconnect_callback = nullptr;
        // Callback function that gets executed when a message is received via the websocket.
        std::function<void(WebSocketServer *ws_server, int client_fd, httpd_ws_frame_t &ws_pkt)>
            message_received_callback = nullptr;
    };

    /**
     * Constructor.
     */
    WebSocketServer(WebSocketManagerConfig config_in) : config_(config_in) {};

    /**
     * Default constructor.
     */
    WebSocketServer() {};

    bool Init();
    bool Update();

    /**
     * Send a message to all clients currently connected to this websocket.
     * @param[in] message Null-terminated string to send.
     * @param[in] len_bytes Optional value for length of message to send, in case the full string in message should not
     * be sent. Does not add a null terminator.
     */
    void BroadcastMessage(const char *message, int16_t len_bytes = -1);

    /**
     * Send a message to a specific client matching the provided client file descriptor.
     * @param[in] client_fd Websocket file descriptor for the client to send the message to.
     * @param[in] message Null-terminated string to send.
     * @param[in] len_bytes Optional value for length of message to send, in case the full string in message should not
     * be sent. Does not add a null terminator.
     * @retval Result of httpd_ws_send_frame_async.
     */
    esp_err_t SendMessage(int client_fd, const char *message, int16_t len_bytes = -1);

    /**
     * Handler function that gets called with all HTTP requests made to the web socket.
     * @param[in] req Incoming HTTP request.
     * @retval ESP_OK if request was handled successfully, ESP_FAIL if connection should be rejected.
     */
    esp_err_t Handler(httpd_req_t *req);

    /**
     * Looks up a currently connected client by its websocket file descriptor and removes it from the pool of connected
     * clients.
     * @param[in] client_fd File descriptor for the websocket to remove from the pool, obtained with
     * httpd_req_to_sockfd(req).
     * @retval True if the client was successfully removed, false if the provided client_fd wasn't a match for any
     * currently connected websocket clients.
     */
    bool RemoveClient(int client_fd);

   private:
    struct WSClientInfo {
        bool in_use = false;
        int client_fd = 0;
        uint32_t last_message_timestamp_ms = 0;
    };

    /**
     * Adds a file descriptor for a websocket client to the currently tracked pool of open websockets.
     * @param[in] client_fd File descriptor for a newly opened websocket, obtained with httpd_req_to_sockfd(req).
     * @retval True if client was successfully added to the pool, false if already tracking the maximum number of
     * clients.
     */
    bool AddClient(int client_fd);

        bool UpdateActivityTimer(int client_fd);

    WebSocketManagerConfig config_;

    WSClientInfo clients_[kMaxNumClients] = {0};
};

#endif /* WEBSOCKET_MANAGER_HH_ */