#include "adsbee_server.hh"

#include "comms.hh"
#include "esp_http_server.h"
#include "nvs_flash.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "task_priorities.hh"

// #define VERBOSE_DEBUG

// This will cause weird crashes if it's too small to support full size SPI transfers!
static const uint32_t kSPIRxTaskStackDepthBytes = 6 * 4096;
static const uint16_t kGDL90Port = 4000;
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
/** End "Pass-Through" functions. **/

bool ADSBeeServer::Init() {
    if (!pico.Init()) {
        CONSOLE_ERROR("ADSBeeServer::Init", "SPI Coprocessor initialization failed.");
        return false;
    }

    spi_receive_task_should_exit_ = false;
    xTaskCreatePinnedToCore(esp_spi_receive_task, "spi_receive_task", kSPIRxTaskStackDepthBytes, NULL,
                            kSPIReceiveTaskPriority, NULL, kSPIReceiveTaskCore);

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

    // Initialize Non Volatile Storage Flash, used by WiFi library.
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    if (!comms_manager.WiFiInit()) {
        CONSOLE_ERROR("ADSBeeServer::Init", "Failed to initialize WiFi.");
        return false;
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
    return ret;
}

bool ADSBeeServer::HandleRawTransponderPacket(RawTransponderPacket &raw_packet) {
    bool ret = true;
    if (!transponder_packet_queue.Push(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Push to transponder packet queue failed. May have overflowed?");
        ret = false;
    }

    if (!comms_manager.WiFiStationSendRawTransponderPacket(raw_packet)) {
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

// TCP server task
void ADSBeeServer::TCPServerTask(void *pvParameters) {
    int addr_family = AF_INET;
    int ip_protocol = 0;
    struct sockaddr_in dest_addr;

    dest_addr.sin_addr.s_addr = htonl(INADDR_ANY);
    dest_addr.sin_family = AF_INET;
    dest_addr.sin_port = htons(kNetworkControlPort);
    ip_protocol = IPPROTO_IP;

    int listen_sock = socket(addr_family, SOCK_STREAM, ip_protocol);
    if (listen_sock < 0) {
        CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Unable to create socket: errno %d", errno);
        vTaskDelete(NULL);
        return;
    }
    // Set SO_REUSEADDR option
    setsockopt(listen_sock, SOL_SOCKET, SO_REUSEADDR, &kTCPServerSockOptReuseAddr, sizeof(kTCPServerSockOptReuseAddr));

    int err = bind(listen_sock, (struct sockaddr *)&dest_addr, sizeof(dest_addr));
    if (err != 0) {
        CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Socket unable to bind: errno %d", errno);
        goto TCP_SERVER_TASK_CLEAN_UP;
    }

    err = listen(listen_sock, 1);
    if (err != 0) {
        CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error occurred during listen: errno %d", errno);
        goto TCP_SERVER_TASK_CLEAN_UP;
    }

    while (1) {
        CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Socket listening");

        struct sockaddr_storage source_addr;
        socklen_t addr_len = sizeof(source_addr);
        int sock = accept(listen_sock, (struct sockaddr *)&source_addr, &addr_len);
        if (sock < 0) {
            CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Unable to accept connection: errno %d", errno);
            break;
        }

        // Set socket to non-blocking mode
        fcntl(sock, F_SETFL, O_NONBLOCK);

        // Set keep-alive properties
        setsockopt(sock, SOL_SOCKET, SO_KEEPALIVE, &kTCPServerSockOptKeepAlive, sizeof(int));
        setsockopt(sock, IPPROTO_TCP, TCP_KEEPIDLE, &kTCPServerSockOptKeepIdleTimeoutSec, sizeof(int));
        setsockopt(sock, IPPROTO_TCP, TCP_KEEPINTVL, &kTCPServerSockOptKeepAliveIntervalSec, sizeof(int));
        setsockopt(sock, IPPROTO_TCP, TCP_KEEPCNT, &kTCPServerSockOptMaxFailedKeepAliveCount, sizeof(int));

        // Convert ip address to string

        if (source_addr.ss_family == PF_INET) {
            // Display IPv4 address.
            char addr_str[128];
            inet_ntoa_r(((struct sockaddr_in *)&source_addr)->sin_addr, addr_str, sizeof(addr_str) - 1);
            CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Socket accepted ip address: %s", addr_str);
        }

        // Handle received data
        while (1) {
            fd_set read_fds;
            struct timeval tv = {.tv_sec = kTCPServerSockSelectTimeoutSec, .tv_usec = 0};

            FD_ZERO(&read_fds);
            FD_SET(sock, &read_fds);

            int select_result = select(sock + 1, &read_fds, NULL, NULL, &tv);

            if (select_result < 0) {
                CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error in select: errno %d", errno);
                break;
            } else if (select_result == 0) {
                // Timeout occurred, no data available
                continue;
            }

            // Data is available to read
            uint8_t rx_buffer[128];
            int len = recv(sock, rx_buffer, sizeof(rx_buffer) - 1, 0);

            if (len < 0) {
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                    // No data available right now, try again later
                    continue;
                }
                // Some other error occurred
                CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error occurred during receiving: errno %d", errno);
                break;
            } else if (len == 0) {
                CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Connection closed by peer");
                break;
            }

            // Process received data
            rx_buffer[len] = 0;  // Null-terminate
            CONSOLE_INFO("ADSBeeServer::TCPServerTask", "Received %d bytes: %s", len, rx_buffer);

            // Echo received data back
            int err = send(sock, rx_buffer, len, 0);
            if (err < 0) {
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                    // Socket buffer is full, try again later
                    vTaskDelay(pdMS_TO_TICKS(10));
                    continue;
                }
                CONSOLE_ERROR("ADSBeeServer::TCPServerTask", "Error occurred during sending: errno %d", errno);
                break;
            }
        }

        shutdown(sock, 0);
        close(sock);
    }

TCP_SERVER_TASK_CLEAN_UP:
    close(listen_sock);
    vTaskDelete(NULL);
}

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

bool ADSBeeServer::TCPServerInit() {
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    // Increase stack size if needed for handling larger files
    config.stack_size = 8192;

    httpd_handle_t server = NULL;

    if (httpd_start(&server, &config) == ESP_OK) {
        // Root URI handler (HTML)
        httpd_uri_t root = {.uri = "/", .method = HTTP_GET, .handler = root_handler, .user_ctx = NULL};
        httpd_register_uri_handler(server, &root);

        // CSS URI handler
        httpd_uri_t css = {.uri = "/style.css", .method = HTTP_GET, .handler = css_handler, .user_ctx = NULL};
        httpd_register_uri_handler(server, &css);
    }

    xTaskCreatePinnedToCore(tcp_server_task, "tcp_server", 4096, NULL, kTCPServerTaskPriority, NULL,
                            kTCPServerTaskCore);

    return server;
}