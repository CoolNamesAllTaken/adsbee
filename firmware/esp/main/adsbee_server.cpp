#include "adsbee_server.hh"

#include "comms.hh"
#include "nvs_flash.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "task_priorities.hh"
#include "unit_conversions.hh"

// #define VERBOSE_DEBUG

static const uint16_t kGDL90Port = 4000;

static const uint32_t kNetworkConsoleWelcomeMessageMaxLen = 1000;

/* obsolete */
static const uint16_t kNetworkControlPort = 3333;  // NOTE: This must match the port number used in index.html!

// TCP Server socket options
static const int kTCPServerSockOptReuseAddr = true;  // Enable TCP server to reuse socket addresses.
static const int kTCPServerSockOptKeepAlive = true;  // Enable TCP socket keepalive for TCP server.
// Number of seconds socket is idle before sending keepalive probes.
static const int kTCPServerSockOptKeepIdleTimeoutSec = 5;
// Number of seconds betwen keepalive packets.
static const int kTCPServerSockOptKeepAliveIntervalSec = 5;
// Number of failed keepalive probes before closing socket.
static const int kTCPServerSockOptMaxFailedKeepAliveCount = 3;
// Number of seconds to wait before giving up on selecting a TCP socket.
static const int kTCPServerSockSelectTimeoutSec = 1;
/* end obsolete */

// Embedded files from the web folder.
extern const uint8_t index_html_start[] asm("_binary_index_html_start");
extern const uint8_t index_html_end[] asm("_binary_index_html_end");
extern const uint8_t style_css_start[] asm("_binary_style_css_start");
extern const uint8_t style_css_end[] asm("_binary_style_css_end");

GDL90Reporter gdl90;

/** "Pass-Through" functions used to access member functions in callbacks. **/

void esp_spi_receive_task(void *pvParameters) {
    adsbee_server.SPIReceiveTask();  // Only returns during DeInit.
    vTaskDelete(NULL);               // Delete this task.
}

void tcp_server_task(void *pvParameters) { adsbee_server.TCPServerTask(pvParameters); }
// esp_err_t console_ws_handler(httpd_req_t *req) { return adsbee_server.NetworkConsoleWebSocketHandler(req); }
void console_ws_close_fd(httpd_handle_t hd, int sockfd) {
    adsbee_server.network_console.RemoveClient(sockfd);
    close(sockfd);
}
/** End "Pass-Through" functions. **/

bool ADSBeeServer::Init() {
    if (!pico.Init()) {
        CONSOLE_ERROR("ADSBeeServer::Init", "SPI Coprocessor initialization failed.");
        return false;
    }

    network_console_rx_queue = xQueueCreate(kNetworkConsoleQueueLen, sizeof(NetworkConsoleMessage));
    network_console_tx_queue = xQueueCreate(kNetworkConsoleQueueLen, sizeof(NetworkConsoleMessage));

    spi_receive_task_should_exit_ = false;
    xTaskCreatePinnedToCore(esp_spi_receive_task, "spi_receive_task", kSPIReceiveTaskStackSizeBytes, NULL,
                            kSPIReceiveTaskPriority, NULL, kSPIReceiveTaskCore);

    // Initialize Non Volatile Storage Flash, used by WiFi library.
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    while (true) {
        if (!pico.Read(ObjectDictionary::kAddrSettingsData, settings_manager.settings)) {
            CONSOLE_ERROR("ADSBeeServer::Init", "Failed to read settings from Pico on startup.");
            vTaskDelay(500 / portTICK_PERIOD_MS);  // Delay for 0.5s before retry.
            continue;
        } else {
            settings_manager.Print();
            settings_manager.Apply();
            break;
        }
    }

    // if (!comms_manager.WiFiInit()) {
    //     CONSOLE_ERROR("ADSBeeServer::Init", "Failed to initialize WiFi.");
    //     return false;
    // }

    TCPServerInit();

    return true;
}

bool ADSBeeServer::Update() {
    bool ret = true;
    // Do NOT call pico.Update() from here since that's already taken care of by the SPIReceiveTask.
    // Update the LED here so it has better time resolution than it would in the SPI task, which blocks frequently.
    pico.UpdateNetworkLED();

    uint32_t timestamp_ms = get_time_since_boot_ms();
    // Prune aircraft dictionary. Need to do this up front so that we don't end up with a negative timestamp delta
    // caused by packets being ingested more recently than the timestamp we take at the beginning of this function.
    if (timestamp_ms - last_aircraft_dictionary_update_timestamp_ms_ > kAircraftDictionaryUpdateIntervalMs) {
        uint32_t scratch;
        if (!pico.Read(ObjectDictionary::Address::kAddrScratch, scratch)) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Read of Pico scratch failed.");
        }

        aircraft_dictionary.Update(timestamp_ms);
        last_aircraft_dictionary_update_timestamp_ms_ = timestamp_ms;
        CONSOLE_INFO("ADSBeeServer::Update", "\t %d clients, %d aircraft, %lu squitter, %lu extended squitter",
                     comms_manager.GetNumWiFiClients(), aircraft_dictionary.GetNumAircraft(),
                     aircraft_dictionary.stats.valid_squitter_frames,
                     aircraft_dictionary.stats.valid_extended_squitter_frames);
    }

    // Ingest new packets into the dictionary.
    RawTransponderPacket raw_packet;
    while (transponder_packet_queue.Pop(raw_packet)) {
        DecodedTransponderPacket decoded_packet = DecodedTransponderPacket(raw_packet);
#ifdef VERBOSE_DEBUG
        if (raw_packet.buffer_len_bits == DecodedTransponderPacket::kExtendedSquitterPacketLenBits) {
            CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%08lx|%08lx|%04lx RSSI=%ddBm MLAT=%llu",
                         raw_packet.buffer[0], raw_packet.buffer[1], raw_packet.buffer[2],
                         (raw_packet.buffer[3]) >> (4 * kBitsPerNibble), raw_packet.sigs_dbm,
                         raw_packet.mlat_48mhz_64bit_counts);
        } else {
            CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%06lx RSSI=%ddBm MLAT=%llu",
                         raw_packet.buffer[0], (raw_packet.buffer[1]) >> (2 * kBitsPerNibble), raw_packet.sigs_dbm,
                         raw_packet.mlat_48mhz_64bit_counts);
        }
        CONSOLE_INFO("ADSBeeServer::Update", "\tdf=%d icao_address=0x%06lx", decoded_packet.GetDownlinkFormat(),
                     decoded_packet.GetICAOAddress());
#endif

        if (aircraft_dictionary.IngestDecodedTransponderPacket(decoded_packet)) {
            // NOTE: Pushing to the reporting queue here means that we only will report validated packets!
            // comms_manager.transponder_packet_reporting_queue.Push(decoded_packet);
#ifdef VERBOSE_DEBUG
            CONSOLE_INFO("ADSBeeServer::Update", "\taircraft_dictionary: %d aircraft",
                         aircraft_dictionary.GetNumAircraft());
#endif
        }
    }

    // Broadcast aircraft locations to connected WiFi clients over GDL90.
    if (timestamp_ms - last_gdl90_report_timestamp_ms_ > kGDL90ReportingIntervalMs) {
        last_gdl90_report_timestamp_ms_ = timestamp_ms;
        if (!ReportGDL90()) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Encountered error while reporting GDL90.");
            ret = false;
        }
    }

    NetworkConsoleMessage message;
    while (xQueueReceive(network_console_rx_queue, &message, 0) == pdTRUE) {
        // Non-blocking receive of network console messages.
        // Write message contents to Pico console, requiring ack.
        if (!pico.Write(ObjectDictionary::kAddrConsole, *(message.buf), true, message.buf_len)) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Failed to write network console message to Pico with contents: %s.",
                          message.buf);
        }
        message.Destroy();  // Free the message buffer to prevent memory leaks.
    }

    network_console.Update();
    // // Prune inactive network console clients.
    // timestamp_ms = get_time_since_boot_ms();  // Refresh timestamp to avoid negative values for time since last
    // message
    //                                           // (except for wraps)
    // for (uint16_t i = 0; i < kNetworkConsoleMaxNumClients; i++) {
    //     uint32_t time_since_last_message_ms = timestamp_ms - network_console_clients[i].last_message_timestamp_ms;
    //     if (network_console_clients[i].in_use && time_since_last_message_ms > kNetworkConsoleInactivityTimeoutMs) {
    //         // Client is in use and has timed out.
    //         int client_fd = network_console_clients[i].client_fd;
    //         CONSOLE_WARNING("ADSBeeServer::Update", "Network console client with fd %d timed out after %lu ms.",
    //                         client_fd, time_since_last_message_ms);
    //         NetworkConsoleRemoveWebsocketClient(client_fd);
    //     }
    // }

    return ret;
}

bool ADSBeeServer::HandleRawTransponderPacket(RawTransponderPacket &raw_packet) {
    bool ret = true;
    if (!transponder_packet_queue.Push(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Push to transponder packet queue failed. May have overflowed?");
        transponder_packet_queue.Clear();
        ret = false;
    }

    if (comms_manager.WiFiStationhasIP() && !comms_manager.WiFiStationSendRawTransponderPacket(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Encountered error while sending raw transponder packet to feeds from ESP32 as WiFi station.");
        ret = false;
    }
    return ret;
}

void ADSBeeServer::SPIReceiveTask() {
    CONSOLE_INFO("SPICoprocessor::SPIReceiveTask", "Started SPI receive task.");

    while (!spi_receive_task_should_exit_) {
        // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received by using
        // max delay.
        pico.Update();
    }

    CONSOLE_INFO("esp_spi_receive_task", "Received exit signal, ending SPI receive task.");
}

bool ADSBeeServer::ReportGDL90() {
    CommsManager::NetworkMessage message;
    message.port = kGDL90Port;

    // Heartbeat Message
    message.len = gdl90.WriteGDL90HeartbeatMessage(message.data, get_time_since_boot_ms() / 1000,
                                                   aircraft_dictionary.stats.valid_extended_squitter_frames);
    comms_manager.WiFiAccessPointSendMessageToAllStations(message);

    // Ownship Report
    GDL90Reporter::GDL90TargetReportData ownship_data;
    // TODO: Actually fill out ownship data!
    // message.len = gdl90.WriteGDL90TargetReportMessage(message.data, ownship_data, true);
    comms_manager.WiFiAccessPointSendMessageToAllStations(message);

    // Traffic Reports
    uint16_t aircraft_index = 0;  // Just used for error reporting.
    for (auto &itr : aircraft_dictionary.dict) {
        const Aircraft &aircraft = itr.second;
        printf("\t%s: %.5f %.5f %ld\r\n", aircraft.callsign, aircraft.latitude_deg, aircraft.longitude_deg,
               aircraft.baro_altitude_ft);
        message.len = gdl90.WriteGDL90TargetReportMessage(message.data, aircraft, false);
        if (settings_manager.settings.wifi_ap_enabled &&
            !comms_manager.WiFiAccessPointSendMessageToAllStations(message)) {
            CONSOLE_ERROR("ADSBeeServer::ReportGDL90", "Failed to send info about aircraft %d to all clients.",
                          aircraft_index);
        }
        aircraft_index++;
    }
    return true;
}

// void ADSBeeServer::TCPServerTask(void *pvParameters) {
//     int addr_family = AF_INET;
//     int ip_protocol = 0;
//     struct sockaddr_in dest_addr;

//     dest_addr.sin_addr.s_addr = htonl(INADDR_ANY);
//     dest_addr.sin_family = AF_INET;
//     dest_addr.sin_port = htons(kNetworkControlPort);
//     ip_protocol = IPPROTO_IP;

//     int listen_sock = socket(addr_family, SOCK_STREAM, ip_protocol);
//     if (listen_sock < 0) {
//         CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Unable to create socket: errno %d", errno);
//         vTaskDelete(NULL);
//         return;
//     }

//     int err = bind(listen_sock, (struct sockaddr *)&dest_addr, sizeof(dest_addr));
//     if (err != 0) {
//         CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Socket unable to bind: errno %d", errno);
//         close(listen_sock);
//         vTaskDelete(NULL);
//         return;
//     }

//     err = listen(listen_sock, 1);
//     if (err != 0) {
//         CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error occurred during listen: errno %d", errno);
//         close(listen_sock);
//         vTaskDelete(NULL);
//         return;
//     }

//     while (1) {
//         CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Socket listening");

//         struct sockaddr_storage source_addr;
//         socklen_t addr_len = sizeof(source_addr);
//         int sock = accept(listen_sock, (struct sockaddr *)&source_addr, &addr_len);
//         if (sock < 0) {
//             CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Unable to accept connection: errno %d", errno);
//             break;
//         }

//         // Display IPv4 address.
//         char addr_str[128];
//         inet_ntoa_r(((struct sockaddr_in *)&source_addr)->sin_addr, addr_str, sizeof(addr_str) - 1);
//         CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Socket accepted ip address: %s", addr_str);

//         // Handle received data
//         while (1) {
//             // Data is available to read
//             uint8_t rx_buffer[128];
//             int len = recv(sock, rx_buffer, sizeof(rx_buffer) - 1, 0);

//             if (len < 0) {
//                 if (errno == EAGAIN || errno == EWOULDBLOCK) {
//                     // No data available right now, try again later
//                     continue;
//                 }
//                 // Some other error occurred
//                 CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error occurred during receiving: errno %d", errno);
//                 break;
//             } else if (len == 0) {
//                 CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Connection closed by peer");
//                 break;
//             }

//             // Process received data
//             rx_buffer[len] = 0;  // Null-terminate
//             CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Received %d bytes: %s", len, rx_buffer);
//         }

//         shutdown(sock, 0);
//         close(sock);
//     }
// }

static esp_err_t root_handler(httpd_req_t *req) {
    httpd_resp_send(req, (const char *)index_html_start, index_html_end - index_html_start);
    return ESP_OK;
}

static esp_err_t css_handler(httpd_req_t *req) {
    // Set the CSS content type
    httpd_resp_set_type(req, "text/css");

    // Send the CSS file
    httpd_resp_send(req, (const char *)style_css_start, style_css_end - style_css_start);

    return ESP_OK;
}

// // Function to broadcast message to all connected clients
// void ADSBeeServer::NetworkConsoleBroadcastMessage(const char *message) {
//     for (int i = 0; i < kNetworkConsoleMaxNumClients; i++) {
//         if (network_console_clients[i].in_use) {
//             esp_err_t ret = NetworkConsoleSendMessage(network_console_clients[i].client_fd, message);
//             if (ret != ESP_OK) {
//                 CONSOLE_ERROR("ADSBeeServer::NetworkConsoleBroadcastMessage", "Failed to send message to client %d:
//                 %d",
//                               i, ret);
//                 // If send failed, assume client disconnected
//                 NetworkConsoleRemoveWebsocketClient(network_console_clients[i].client_fd);
//             }
//         }
//     }
// }

// bool ADSBeeServer::NetworkConsoleAddWebSocketClient(int client_fd) {
//     for (int i = 0; i < kNetworkConsoleMaxNumClients; i++) {
//         if (!network_console_clients[i].in_use) {
//             network_console_clients[i].in_use = true;
//             network_console_clients[i].client_fd = client_fd;
//             network_console_clients[i].last_message_timestamp_ms = get_time_since_boot_ms();
//             CONSOLE_INFO("ADSBeeServer::NetworkConsoleAddWebSocketClient", "New client stored at index %d", i);
//             return true;
//         }
//     }
//     CONSOLE_ERROR("ADSBeeServer:NetworkConsoleAddWebSocketClient",
//                   "Can't connect additional clients, already reached maximum of %d.", kNetworkConsoleMaxNumClients);
//     return false;
// }

// bool ADSBeeServer::NetworkConsoleRemoveWebsocketClient(int client_fd) {
//     for (int i = 0; i < kNetworkConsoleMaxNumClients; i++) {
//         if (network_console_clients[i].in_use && network_console_clients[i].client_fd == client_fd) {
//             network_console_clients[i].in_use = false;
//             network_console_clients[i].client_fd = -1;
//             CONSOLE_INFO("ADSBeeServer::NetworkConsoleRemoveWebSocketClient", "Client removed from index %d", i);
//             return true;
//         }
//     }
//     CONSOLE_ERROR("ADSBeeServer::NetworkConsoleRemoveWebSocketClient", "Client with fd %d not found.", client_fd);
//     return false;
// }

// Function to send message to a specific client
// esp_err_t ADSBeeServer::NetworkConsoleSendMessage(int client_fd, const char *message) {
//     httpd_ws_frame_t ws_pkt = {.final = true,
//                                .fragmented = false,
//                                .type = HTTPD_WS_TYPE_TEXT,
//                                .payload = (uint8_t *)message,
//                                .len = strlen(message)};

//     return httpd_ws_send_frame_async(server, client_fd, &ws_pkt);
// }

// bool ADSBeeServer::NetworkConsoleUpdateActivityTimer(int client_fd) {
//     for (int i = 0; i < kNetworkConsoleMaxNumClients; i++) {
//         if (network_console_clients[i].client_fd == client_fd) {
//             network_console_clients[i].last_message_timestamp_ms = get_time_since_boot_ms();
//             return true;
//         }
//     }
//     return false;  // Couldn't find client.
// }

// esp_err_t ADSBeeServer::NetworkConsoleWebSocketHandler(httpd_req_t *req) {
//     int client_fd = httpd_req_to_sockfd(req);

//     if (req->method == HTTP_GET) {
//         CONSOLE_INFO("ADSBeeServer::ConsoleWebsocketHandler", "Handshake done, the new connection was opened");
//         if (!NetworkConsoleAddWebSocketClient(client_fd)) {
//             CONSOLE_ERROR("ADSBee::NetworkConsoleWebSocketHandler", "Rejecting websocket connection.");
//             // Send a close frame
//             httpd_ws_frame_t ws_pkt = {
//                 .final = true, .fragmented = false, .type = HTTPD_WS_TYPE_CLOSE, .payload = NULL, .len = 0};

//             httpd_ws_send_frame(req, &ws_pkt);

//             // Return error to reject the connection
//             return ESP_FAIL;
//         }
//         char welcome_message[kNetworkConsoleWelcomeMessageMaxLen];
//         snprintf(welcome_message, kNetworkConsoleWelcomeMessageMaxLen,
//                  "\r\n █████  ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
//                  "\r\n██   ██ ██   ██ ██      ██   ██ ██      ██          ███ ██  ████ ██   ██ ██  ████ "
//                  "\r\n███████ ██   ██ ███████ ██████  █████   █████        ██ ██ ██ ██  ██████ ██ ██ ██ "
//                  "\r\n██   ██ ██   ██      ██ ██   ██ ██      ██           ██ ████  ██      ██ ████  ██ "
//                  "\r\n██   ██ ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
//                  "\r\n\r\nFirmware Version: %d.%d.%d\r\nAP SSID: %s\r\n",
//                  object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
//                  object_dictionary.kFirmwareVersionPatch, settings_manager.settings.wifi_ap_ssid);
//         welcome_message[kNetworkConsoleWelcomeMessageMaxLen] = '\0';  // Null terminate for safety.
//         NetworkConsoleSendMessage(client_fd, welcome_message);
//         return ESP_OK;
//     }
//     httpd_ws_frame_t ws_pkt;
//     uint8_t *buf = NULL;
//     memset(&ws_pkt, 0, sizeof(httpd_ws_frame_t));
//     ws_pkt.type = HTTPD_WS_TYPE_TEXT;
//     /* Set max_len = 0 to get the frame len */
//     esp_err_t ret = httpd_ws_recv_frame(req, &ws_pkt, 0);
//     if (ret != ESP_OK) {
//         CONSOLE_ERROR("ADSBeeServer::ConsoleWebsocketHandler", "httpd_ws_recv_frame failed to get frame len with
//         %d.",
//                       ret);
//         return ret;
//     }
//     CONSOLE_INFO("ADSBeeServer::ConsoleWebsocketHandler", "frame len is %d.", ws_pkt.len);
//     if (ws_pkt.len) {
//         /* ws_pkt.len + 1 is for NULL termination as we are expecting a string */
//         buf = (uint8_t *)calloc(1, ws_pkt.len + 1);
//         if (buf == NULL) {
//             CONSOLE_ERROR("ADSBeeServer::ConsoleWebsocketHandler", "Failed to calloc memory for buf.");
//             return ESP_ERR_NO_MEM;
//         }
//         ws_pkt.payload = buf;
//         /* Set max_len = ws_pkt.len to get the frame payload */
//         ret = httpd_ws_recv_frame(req, &ws_pkt, ws_pkt.len);
//         if (ret != ESP_OK) {
//             CONSOLE_ERROR("ADSBeeServer::ConsoleWebsocketHandler", "httpd_ws_recv_frame failed with %d.", ret);
//             free(buf);
//             NetworkConsoleRemoveWebsocketClient(client_fd);
//             return ret;
//         }

//         NetworkConsoleUpdateActivityTimer(client_fd);
//         CONSOLE_INFO("ADSBeeServer::ConsoleWebsocketHandler", "Got packet with message: %s", ws_pkt.payload);

//         // Forward the network console message to the RP2040.
//         NetworkConsoleMessage message = NetworkConsoleMessage((char *)ws_pkt.payload, (uint16_t)ws_pkt.len);
//         int err = xQueueSend(network_console_rx_queue, &message, 0);
//         if (err == errQUEUE_FULL) {
//             CONSOLE_WARNING("ADSBeeServer::NetworkConsoleWebSocketHandler", "Overflowed network console rx queue.");
//             xQueueReset(network_console_rx_queue);
//             return ESP_FAIL;
//         } else if (err != pdTRUE) {
//             CONSOLE_WARNING("ADSBeeServer::NetworkConsoleWebSocketHandler",
//                             "Pushing network console message to network console rx queue resulted in error %d.",
//                             err);
//             return ESP_FAIL;
//         }
//     }

//     free(buf);
//     return ret;
// }

void NetworkConsolePostConnectCallback(WebSocketServer *ws_server, int client_fd) {
    char welcome_message[kNetworkConsoleWelcomeMessageMaxLen];
    snprintf(welcome_message, kNetworkConsoleWelcomeMessageMaxLen,
             "\r\n █████  ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
             "\r\n██   ██ ██   ██ ██      ██   ██ ██      ██          ███ ██  ████ ██   ██ ██  ████ "
             "\r\n███████ ██   ██ ███████ ██████  █████   █████        ██ ██ ██ ██  ██████ ██ ██ ██ "
             "\r\n██   ██ ██   ██      ██ ██   ██ ██      ██           ██ ████  ██      ██ ████  ██ "
             "\r\n██   ██ ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
             "\r\n\r\nFirmware Version: %d.%d.%d\r\nAP SSID: %s\r\n",
             object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
             object_dictionary.kFirmwareVersionPatch, settings_manager.settings.wifi_ap_ssid);
    welcome_message[kNetworkConsoleWelcomeMessageMaxLen] = '\0';  // Null terminate for safety.
    ws_server->SendMessage(client_fd, welcome_message);
}

void NetworkConsoleMessageReceivedCallback(WebSocketServer *ws_server, int client_fd, httpd_ws_frame_t &ws_pkt) {
    // Forward the network console message to the RP2040.
    ADSBeeServer::NetworkConsoleMessage message =
        ADSBeeServer::NetworkConsoleMessage((char *)ws_pkt.payload, (uint16_t)ws_pkt.len);
    int err = xQueueSend(adsbee_server.network_console_rx_queue, &message, 0);
    if (err == errQUEUE_FULL) {
        CONSOLE_WARNING("NetworkConsoleMessageReceivedCallback", "Overflowed network console rx queue.");
        xQueueReset(adsbee_server.network_console_rx_queue);
    } else if (err != pdTRUE) {
        CONSOLE_WARNING("NetworkConsoleMessageReceivedCallback",
                        "Pushing network console message to network console rx queue resulted in error %d.", err);
    }
}

bool ADSBeeServer::TCPServerInit() {
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.stack_size = 4 * 4096;  // Extra stack needed for calls to SPI peripheral and handling large files.
    config.close_fn = console_ws_close_fd;

    if (httpd_start(&server, &config) == ESP_OK) {
        // Root URI handler (HTML)
        httpd_uri_t root = {.uri = "/", .method = HTTP_GET, .handler = root_handler, .user_ctx = NULL};
        httpd_register_uri_handler(server, &root);

        // CSS URI handler
        httpd_uri_t css = {.uri = "/style.css", .method = HTTP_GET, .handler = css_handler, .user_ctx = NULL};
        httpd_register_uri_handler(server, &css);

        // Network console Websocket handler
        // httpd_uri_t console_ws = {.uri = "/console",
        //                           .method = HTTP_GET,
        //                           .handler = console_ws_handler,
        //                           .user_ctx = NULL,
        //                           .is_websocket = true};
        // httpd_register_uri_handler(server, &console_ws);
        network_console = WebSocketServer({.label = "Network Console",
                                           .server = server,
                                           .uri = "/console",
                                           .num_clients_allowed = 3,
                                           .post_connect_callback = NetworkConsolePostConnectCallback,
                                           .message_received_callback = NetworkConsoleMessageReceivedCallback});
        network_console.Init();
    }

    // xTaskCreatePinnedToCore(tcp_server_task, "tcp_server", kTCPServerTaskStackSizeBytes, NULL,
    // kTCPServerTaskPriority,
    //                         NULL, kTCPServerTaskCore);

    return server != nullptr;
}