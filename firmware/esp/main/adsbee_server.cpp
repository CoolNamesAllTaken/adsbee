#include "adsbee_server.hh"

#include "comms.hh"
#include "json_utils.hh"
#include "nvs_flash.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "task_priorities.hh"
#include "unit_conversions.hh"

// #define VERBOSE_DEBUG

static const uint16_t kGDL90Port = 4000;

static const uint16_t kNetworkConsoleWelcomeMessageMaxLen = 1000;
static const uint16_t kNetworkMetricsMessageMaxLen = 1000;
static const uint16_t kNumTransponderPacketSources = 3;

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
extern const uint8_t favicon_png_start[] asm("_binary_favicon_png_start");
extern const uint8_t favicon_png_end[] asm("_binary_favicon_png_end");

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

    comms_manager.Init();  // Initialize prerequisites for Ethernet and WiFi.

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
                     aircraft_dictionary.metrics.valid_squitter_frames,
                     aircraft_dictionary.metrics.valid_extended_squitter_frames);

        // ESP32 can't see number of attempted demodulations, so steal that from RP2040 metrics dictionary.
        AircraftDictionary::Metrics combined_metrics = aircraft_dictionary.metrics;
        combined_metrics.demods_1090 = adsbee_server.rp2040_aircraft_dictionary_metrics.demods_1090;
        for (uint16_t i = 0; i < AircraftDictionary::kMaxNumSources; i++) {
            combined_metrics.demods_1090_by_source[i] +=
                adsbee_server.rp2040_aircraft_dictionary_metrics.demods_1090_by_source[i];
        }
        // Broadcast dictionary metrics over the metrics Websocket.
        char metrics_message[AircraftDictionary::Metrics::kMetricsJSONMaxLen];
        snprintf(metrics_message, kNetworkMetricsMessageMaxLen, "{ \"aircraft_dictionary_metrics\": ");
        combined_metrics.ToJSON(metrics_message + strlen(metrics_message),
                                kNetworkMetricsMessageMaxLen - strlen(metrics_message));
        snprintf(metrics_message + strlen(metrics_message), kNetworkMetricsMessageMaxLen - strlen(metrics_message),
                 ", \"server_metrics\": { ");
        // ADSBee Server Metrics
        ArrayToJSON(metrics_message + strlen(metrics_message), kNetworkMetricsMessageMaxLen - strlen(metrics_message),
                    "feed_uri", settings_manager.settings.feed_uris, "\"%s\"", true);
        ArrayToJSON(metrics_message + strlen(metrics_message), kNetworkMetricsMessageMaxLen - strlen(metrics_message),
                    "feed_mps", comms_manager.feed_mps, "%u", false);  // Mo trailing comma.
        snprintf(metrics_message + strlen(metrics_message), kNetworkMetricsMessageMaxLen - strlen(metrics_message),
                 "}}");

        network_metrics.BroadcastMessage(metrics_message, strlen(metrics_message));
    }

    // Ingest new packets into the dictionary.
    RawTransponderPacket raw_packet;
    while (raw_transponder_packet_queue.Pop(raw_packet)) {
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
            // NOTE: Pushing to a queue here will only forward valid packets!
#ifdef VERBOSE_DEBUG
            CONSOLE_INFO("ADSBeeServer::Update", "\taircraft_dictionary: %d aircraft",
                         aircraft_dictionary.GetNumAircraft());
#endif
        }

        // Send decoded transponder packet to feeds.
        if (comms_manager.WiFiStationhasIP() &&
            !comms_manager.WiFiStationSendDecodedTransponderPacket(decoded_packet)) {
            CONSOLE_ERROR(
                "ADSBeeServer::Update",
                "Encountered error while sending decoded transponder packet to feeds from ESP32 as WiFi station.");
            ret = false;
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

    // Receive incoming network console messages from the console websocket.
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

    // Prune inactive WebSocket clients and other housekeeping.
    network_console.Update();

    // Check to see whether the RP2040 sent over new metrics.
    xQueueReceive(rp2040_aircraft_dictionary_metrics_queue, &rp2040_aircraft_dictionary_metrics, 0);

    return ret;
}

bool ADSBeeServer::HandleRawTransponderPacket(RawTransponderPacket &raw_packet) {
    bool ret = true;
    if (!raw_transponder_packet_queue.Push(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Push to transponder packet queue failed. May have overflowed?");
        raw_transponder_packet_queue.Clear();
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
                                                   aircraft_dictionary.metrics.valid_extended_squitter_frames);
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

esp_err_t favicon_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "image/png");
    httpd_resp_set_hdr(req, "Cache-Control", "max-age=2592000, public");  // Cache for 30 days

    esp_err_t res = httpd_resp_send(req, (const char *)favicon_png_start, favicon_png_end - favicon_png_start);
    if (res != ESP_OK) {
        ESP_LOGE("FAVICON", "Failed to send favicon");
        return res;
    }
    return ESP_OK;
}

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
    config.stack_size = kHTTPServerStackSizeBytes;
    config.close_fn = console_ws_close_fd;

    if (httpd_start(&server, &config) == ESP_OK) {
        // Root URI handler (HTML)
        httpd_uri_t root = {.uri = "/", .method = HTTP_GET, .handler = root_handler, .user_ctx = NULL};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &root));

        // CSS URI handler
        httpd_uri_t css = {.uri = "/style.css", .method = HTTP_GET, .handler = css_handler, .user_ctx = NULL};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &css));

        // Favicon URI handler
        httpd_uri_t favicon = {.uri = "/favicon.png", .method = HTTP_GET, .handler = favicon_handler, .user_ctx = NULL};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &favicon));

        network_console = WebSocketServer({.label = "Network Console",
                                           .server = server,
                                           .uri = "/console",
                                           .num_clients_allowed = 3,
                                           .post_connect_callback = NetworkConsolePostConnectCallback,
                                           .message_received_callback = NetworkConsoleMessageReceivedCallback});
        network_console.Init();
        network_metrics = WebSocketServer({.label = "Network Metrics",
                                           .server = server,
                                           .uri = "/metrics",
                                           .num_clients_allowed = 3,
                                           .post_connect_callback = nullptr,
                                           .message_received_callback = nullptr});
        network_metrics.Init();
    }

    // xTaskCreatePinnedToCore(tcp_server_task, "tcp_server", kTCPServerTaskStackSizeBytes, NULL,
    // kTCPServerTaskPriority,
    //                         NULL, kTCPServerTaskCore);

    return server != nullptr;
}