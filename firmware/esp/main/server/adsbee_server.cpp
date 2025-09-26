#include "adsbee_server.hh"

#include "comms.hh"
#include "gdl90/gdl90_utils.hh"
#include "json_utils.hh"
#include "pico.hh"
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

extern GDL90Reporter gdl90;

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

    // Initialize SPI receive task before requesting settings so that we can tend to messages from the RP2040 and stop
    // it from freaking out.
    spi_receive_task_should_exit_ = false;
    xTaskCreatePinnedToCore(esp_spi_receive_task, "spi_receive_task", kSPIReceiveTaskStackSizeBytes, NULL,
                            kSPIReceiveTaskPriority, NULL, kSPIReceiveTaskCore);

    // Initialize prerequisites for Ethernet and WiFi. Needs to be done before settings are applied.
    comms_manager.Init();

    SemaphoreHandle_t settings_read_semaphore = xSemaphoreCreateBinary();
    if (settings_read_semaphore == NULL) {
        CONSOLE_ERROR("ADSBeeServer::Init", "Failed to create settings read semaphore.");
        return false;
    }

    object_dictionary.RequestSCCommand(ObjectDictionary::SCCommandRequestWithCallback{
        .request =
            ObjectDictionary::SCCommandRequest{.command = ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck,
                                               .addr = ObjectDictionary::Address::kAddrSettingsData,
                                               .offset = 0,
                                               .len = sizeof(SettingsManager::Settings)},
        .complete_callback =
            [settings_read_semaphore]() {
                CONSOLE_INFO("ADSBeeServer::Init", "Settings data read from Pico.");
                xSemaphoreGive(settings_read_semaphore);
            },
    });  // Require ack.

    // Wait for the callback to complete
    xSemaphoreTake(settings_read_semaphore, portMAX_DELAY);
    vSemaphoreDelete(settings_read_semaphore);
    settings_manager.Print();
    settings_manager.Apply();

    return TCPServerInit();
}

bool ADSBeeServer::Update() {
    bool ret = true;
    // Do NOT call pico.Update() from here since that's already taken care of by the SPIReceiveTask.
    // Update the LED here so it has better time resolution than it would in the SPI task, which blocks frequently.
    pico.UpdateLED();

    uint32_t timestamp_ms = get_time_since_boot_ms();
    // Prune aircraft dictionary. Need to do this up front so that we don't end up with a negative timestamp delta
    // caused by packets being ingested more recently than the timestamp we take at the beginning of this function.
    if (timestamp_ms - last_aircraft_dictionary_update_timestamp_ms_ > kAircraftDictionaryUpdateIntervalMs) {
        aircraft_dictionary.Update(timestamp_ms);
        last_aircraft_dictionary_update_timestamp_ms_ = timestamp_ms;
        CONSOLE_INFO("ADSBeeServer::Update", "\t %d clients, %d aircraft, %lu squitter, %lu extended squitter",
                     comms_manager.GetNumWiFiClients(), aircraft_dictionary.GetNumAircraft(),
                     aircraft_dictionary.metrics.valid_squitter_frames,
                     aircraft_dictionary.metrics.valid_extended_squitter_frames);

        // ESP32 can't see number of attempted demodulations or raw packets, so steal that from RP2040 metrics
        // dictionary.
        AircraftDictionary::Metrics combined_metrics = aircraft_dictionary.metrics;
        // Steal demods_1090.
        combined_metrics.demods_1090 = adsbee_server.rp2040_aircraft_dictionary_metrics.demods_1090;
        for (uint16_t i = 0; i < AircraftDictionary::kMaxNumSources; i++) {
            combined_metrics.demods_1090_by_source[i] +=
                adsbee_server.rp2040_aircraft_dictionary_metrics.demods_1090_by_source[i];
        }
        // Steal raw_squitter_frames.
        combined_metrics.raw_squitter_frames = adsbee_server.rp2040_aircraft_dictionary_metrics.raw_squitter_frames;
        for (uint16_t i = 0; i < AircraftDictionary::kMaxNumSources; i++) {
            combined_metrics.raw_squitter_frames_by_source[i] +=
                adsbee_server.rp2040_aircraft_dictionary_metrics.raw_squitter_frames_by_source[i];
        }
        // Steal raw_extended_squitter_frames.
        combined_metrics.raw_extended_squitter_frames =
            adsbee_server.rp2040_aircraft_dictionary_metrics.raw_extended_squitter_frames;
        for (uint16_t i = 0; i < AircraftDictionary::kMaxNumSources; i++) {
            combined_metrics.raw_extended_squitter_frames_by_source[i] +=
                adsbee_server.rp2040_aircraft_dictionary_metrics.raw_extended_squitter_frames_by_source[i];
        }
        // Steal UAT metrics.
        combined_metrics.raw_uat_adsb_frames = adsbee_server.rp2040_aircraft_dictionary_metrics.raw_uat_adsb_frames;
        combined_metrics.valid_uat_adsb_frames = adsbee_server.rp2040_aircraft_dictionary_metrics.valid_uat_adsb_frames;
        combined_metrics.raw_uat_uplink_frames = adsbee_server.rp2040_aircraft_dictionary_metrics.raw_uat_uplink_frames;
        combined_metrics.valid_uat_uplink_frames =
            adsbee_server.rp2040_aircraft_dictionary_metrics.valid_uat_uplink_frames;

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

    // Run raw packet ingestion and reporting if queues are >50% full or every 200ms.
    bool at_least_one_queue_half_full =
        (raw_mode_s_packet_in_queue.Length() > raw_mode_s_packet_in_queue.MaxNumElements() / 2) ||
        (raw_uat_adsb_packet_in_queue.Length() > raw_uat_adsb_packet_in_queue.MaxNumElements() / 2) ||
        (raw_uat_uplink_packet_in_queue.Length() > raw_uat_uplink_packet_in_queue.MaxNumElements() / 2);

    if (timestamp_ms - last_raw_packet_process_timestamp_ms_ > kRawPacketProcessingIntervalMs ||
        at_least_one_queue_half_full) {
        last_raw_packet_process_timestamp_ms_ = timestamp_ms;

        // Assemble a CompositeArray of transponder packets to report.
        // NOTE: Rate metering of raw packets is done by upstream RP2040, which only forward packets on the raw
        // packet reporting time interval.
        uint8_t raw_packets_buf[CompositeArray::RawPackets::kMaxLenBytes];
        CompositeArray::RawPackets raw_packets = CompositeArray::PackRawPacketsBuffer(
            raw_packets_buf, sizeof(raw_packets_buf), &(adsbee_server.raw_mode_s_packet_in_queue),
            &(adsbee_server.raw_uat_adsb_packet_in_queue), &(adsbee_server.raw_uat_uplink_packet_in_queue));

        if (!raw_packets.IsValid()) {
            if (raw_packets.len_bytes > sizeof(CompositeArray::RawPackets::Header)) {
                CONSOLE_ERROR("ADSBeeServer::Update",
                              "Invalid CompositeArray of transponder packets (len_bytes = %u). Dropping packets.",
                              raw_packets.len_bytes);
            }
            // Else it's OK to have no packets.
        } else {
            // Add packets to aircraft dictionary and then report them.

            // Mode S Packets
            for (uint16_t i = 0; i < raw_packets.header->num_mode_s_packets; i++) {
                RawModeSPacket &raw_mode_s_packet = raw_packets.mode_s_packets[i];
                DecodedModeSPacket decoded_packet = DecodedModeSPacket(raw_mode_s_packet);
                if (!decoded_packet.is_valid) {
                    CONSOLE_ERROR("ADSBeeServer::Update", "Received invalid Mode S packet.");
                    continue;
                }
#ifdef VERBOSE_DEBUG
                if (raw_mode_s_packet.buffer_len_bytes == RawModeSPacket::kExtendedSquitterPacketLenBytes) {
                    CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%08lx|%08lx|%04lx RSSI=%ddBm MLAT=%llu",
                                 raw_mode_s_packet.buffer[0], raw_mode_s_packet.buffer[1], raw_mode_s_packet.buffer[2],
                                 (raw_mode_s_packet.buffer[3]) >> (4 * kBitsPerNibble), raw_mode_s_packet.sigs_dbm,
                                 raw_mode_s_packet.mlat_48mhz_64bit_counts);
                } else {
                    CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%06lx RSSI=%ddBm MLAT=%llu",
                                 raw_mode_s_packet.buffer[0], (raw_mode_s_packet.buffer[1]) >> (2 * kBitsPerNibble),
                                 raw_mode_s_packet.sigs_dbm, raw_mode_s_packet.mlat_48mhz_64bit_counts);
                }
                CONSOLE_INFO("ADSBeeServer::Update", "\tdf=%d icao_address=0x%06lx", decoded_packet.downlink_format,
                             decoded_packet.icao_address);
#endif

                if (!aircraft_dictionary.IngestDecodedModeSPacket(decoded_packet)) {
                    // NOTE: Pushing to a queue here will only forward valid packets!
                    CONSOLE_ERROR("ADSBeeServer::Update",
                                  "Failed to ingest decoded Mode S packet into aircraft dictionary.");
                }
            }

            // UAT ADSB Packets
            for (uint16_t i = 0; i < raw_packets.header->num_uat_adsb_packets; i++) {
                RawUATADSBPacket &raw_uat_adsb_packet = raw_packets.uat_adsb_packets[i];
                DecodedUATADSBPacket decoded_packet = DecodedUATADSBPacket(raw_uat_adsb_packet);
                if (!decoded_packet.is_valid) {
                    CONSOLE_ERROR("ADSBeeServer::Update", "Received invalid UAT ADSB packet.");
                    continue;
                }
                if (!aircraft_dictionary.IngestDecodedUATADSBPacket(decoded_packet)) {
                    CONSOLE_ERROR("ADSBeeServer::Update",
                                  "Failed to ingest decoded UAT ADSB packet into aircraft dictionary.");
                }
            }

            // UAT Uplink Packets
            // We don't currently digest uplink packets, they just get forwarded.
            // TODO: Add uplink packet forwarding via GDL90.

            // Forward packets to WAN.
            comms_manager.IPWANSendRawPacketCompositeArray(raw_packets_buf);
        }
    }

    // Broadcast aircraft locations to connected WiFi clients over GDL90.
    if (timestamp_ms - last_gdl90_report_timestamp_ms_ > kGDL90ReportingIntervalMs) {
        last_gdl90_report_timestamp_ms_ = timestamp_ms;
        if (comms_manager.WiFiAccessPointHasClients() && !ReportGDL90()) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Encountered error while reporting GDL90.");
            ret = false;
        }
    }

    // Prune inactive WebSocket clients and other housekeeping.
    network_console.Update();

    // Check to see whether the RP2040 sent over new metrics.
    xQueueReceive(rp2040_aircraft_dictionary_metrics_queue, &rp2040_aircraft_dictionary_metrics, 0);

    return ret;
}

void ADSBeeServer::SPIReceiveTask() {
    CONSOLE_INFO("ADSBeeServer::SPIReceiveTask", "Started SPI receive task.");

    while (!spi_receive_task_should_exit_) {
        // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received by using
        // max delay.
        pico.Update();
        if (pico_ll.SPIClaimNextTransaction()) {
            pico_ll.SPIReleaseNextTransaction();
        } else {
            CONSOLE_ERROR("ADSBeeServer::SPIReceiveTask", "Failed to bump SPI context mutex for lower priority tasks.");
        }
    }

    CONSOLE_INFO("esp_spi_receive_task", "Received exit signal, ending SPI receive task.");
}

bool ADSBeeServer::ReportGDL90() {
    if (!settings_manager.settings.core_network_settings.wifi_ap_enabled) {
        return true;  // Nothing to do.
    }

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
    int16_t aircraft_index = -1;  // Just used for error reporting.
    uint8_t aircraft_msg_buf[CommsManager::NetworkMessage::kMaxLenBytes];
    uint16_t aircraft_msg_buf_len = 0;
    for (auto &itr : aircraft_dictionary.dict) {
        aircraft_index++;

        if (ModeSAircraft *mode_s_aircraft = get_if<ModeSAircraft>(&(itr.second)); mode_s_aircraft) {
            if (!mode_s_aircraft->HasBitFlag(ModeSAircraft::kBitFlagPositionValid)) {
                // Don't report aircraft without a valid position.
                continue;
            }
            printf("\t#A %s (0x%06lX): %.5f %.5f %ld\r\n", mode_s_aircraft->callsign, mode_s_aircraft->icao_address,
                   mode_s_aircraft->latitude_deg, mode_s_aircraft->longitude_deg, mode_s_aircraft->baro_altitude_ft);
            aircraft_msg_buf_len = gdl90.WriteGDL90TargetReportMessage(aircraft_msg_buf, *mode_s_aircraft, false);
        } else if (UATAircraft *uat_aircraft = get_if<UATAircraft>(&(itr.second)); uat_aircraft) {
            if (!uat_aircraft->HasBitFlag(UATAircraft::kBitFlagPositionValid)) {
                // Don't report aircraft without a valid position.
                continue;
            }
            printf("\t#U %s (0x%06lX): %.5f %.5f %ld\r\n", uat_aircraft->callsign, uat_aircraft->icao_address,
                   uat_aircraft->latitude_deg, uat_aircraft->longitude_deg, uat_aircraft->baro_altitude_ft);
            aircraft_msg_buf_len = gdl90.WriteGDL90TargetReportMessage(aircraft_msg_buf, *uat_aircraft, false);
        } else {
            CONSOLE_WARNING("CommsManager::ReportCSBee", "Unknown aircraft type in dictionary for UID 0x%lx.",
                            itr.first);
            continue;
        }

        if (message.len + aircraft_msg_buf_len <= CommsManager::NetworkMessage::kMaxLenBytes) {
            // We can tack this aircraft message onto the existing message to save space in the queue.
            memcpy(message.data + message.len, aircraft_msg_buf, aircraft_msg_buf_len);
            message.len += aircraft_msg_buf_len;
        } else {
            // Send the existing message and start a new one.
            if (!comms_manager.WiFiAccessPointSendMessageToAllStations(message)) {
                CONSOLE_ERROR("ADSBeeServer::ReportGDL90", "Failed to send info about aircraft %d to all clients.",
                              aircraft_index);
            }
            memcpy(message.data, aircraft_msg_buf, aircraft_msg_buf_len);
            message.len = aircraft_msg_buf_len;
        }
    }

    // Send any remaining message data.
    if (message.len > 0) {
        if (!comms_manager.WiFiAccessPointSendMessageToAllStations(message)) {
            CONSOLE_ERROR("ADSBeeServer::ReportGDL90", "Failed to send final aircraft message to all clients.");
        }
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
    if (object_dictionary.kFirmwareVersionReleaseCandidate == 0) {
        snprintf(welcome_message, kNetworkConsoleWelcomeMessageMaxLen,
                 "\r\n █████  ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
                 "\r\n██   ██ ██   ██ ██      ██   ██ ██      ██          ███ ██  ████ ██   ██ ██  ████ "
                 "\r\n███████ ██   ██ ███████ ██████  █████   █████        ██ ██ ██ ██  ██████ ██ ██ ██ "
                 "\r\n██   ██ ██   ██      ██ ██   ██ ██      ██           ██ ████  ██      ██ ████  ██ "
                 "\r\n██   ██ ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
                 "\r\n\r\nFirmware Version: %d.%d.%d\r\nAP SSID: %s\r\n",
                 object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                 object_dictionary.kFirmwareVersionPatch, settings_manager.settings.core_network_settings.wifi_ap_ssid);
    } else {
        snprintf(welcome_message, kNetworkConsoleWelcomeMessageMaxLen,
                 "\r\n █████  ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
                 "\r\n██   ██ ██   ██ ██      ██   ██ ██      ██          ███ ██  ████ ██   ██ ██  ████ "
                 "\r\n███████ ██   ██ ███████ ██████  █████   █████        ██ ██ ██ ██  ██████ ██ ██ ██ "
                 "\r\n██   ██ ██   ██      ██ ██   ██ ██      ██           ██ ████  ██      ██ ████  ██ "
                 "\r\n██   ██ ██████  ███████ ██████  ███████ ███████      ██  ██████   █████   ██████  "
                 "\r\n\r\nFirmware Version: %d.%d.%d-rc%d\r\nAP SSID: %s\r\n",
                 object_dictionary.kFirmwareVersionMajor, object_dictionary.kFirmwareVersionMinor,
                 object_dictionary.kFirmwareVersionPatch, object_dictionary.kFirmwareVersionReleaseCandidate,
                 settings_manager.settings.core_network_settings.wifi_ap_ssid);
    }

    welcome_message[kNetworkConsoleWelcomeMessageMaxLen] = '\0';  // Null terminate for safety.
    ws_server->SendMessage(client_fd, welcome_message);
}

void NetworkConsoleMessageReceivedCallback(WebSocketServer *ws_server, int client_fd, httpd_ws_frame_t &ws_pkt) {
    // Forward the network console message to the RP2040.
    char *message = (char *)ws_pkt.payload;
    uint16_t message_len = (uint16_t)ws_pkt.len;
    xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);
    if (object_dictionary.network_console_rx_queue.MaxNumElements() -
            object_dictionary.network_console_rx_queue.Length() <
        message_len) {
        CONSOLE_ERROR("NetworkConsoleMessageReceivedCallback",
                      "Network console tx queue is full, dropping message of length %d.", message_len);
        xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
        return;
    }
    for (uint16_t i = 0; i < ws_pkt.len; i++) {
        if (!object_dictionary.network_console_rx_queue.Enqueue(message[i])) {
            CONSOLE_ERROR("NetworkConsoleMessageReceivedCallback",
                          "Failed to push character %d of network console message to tx queue.", i + 1);
            xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
            return;
        }
    }
    xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
}

bool ADSBeeServer::TCPServerInit() {
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.stack_size = kHTTPServerStackSizeBytes;
    config.close_fn = console_ws_close_fd;

    esp_err_t ret = httpd_start(&server, &config);
    if (ret == ESP_OK) {
        // Root URI handler (HTML)
        httpd_uri_t root = {
            .uri = "/", .method = HTTP_GET, .handler = root_handler, .user_ctx = NULL, .is_websocket = false};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &root));

        // CSS URI handler
        httpd_uri_t css = {
            .uri = "/style.css", .method = HTTP_GET, .handler = css_handler, .user_ctx = NULL, .is_websocket = false};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &css));

        // Favicon URI handler
        httpd_uri_t favicon = {.uri = "/favicon.png",
                               .method = HTTP_GET,
                               .handler = favicon_handler,
                               .user_ctx = NULL,
                               .is_websocket = false};
        ESP_ERROR_CHECK(httpd_register_uri_handler(server, &favicon));

        network_console = WebSocketServer({.label = "Network Console",
                                           .server = server,
                                           .uri = "/console",
                                           .num_clients_allowed = WebSocketServer::kMaxNumClients,
                                           .send_as_binary = true,  // Network console messages can contain binary data.
                                           .post_connect_callback = NetworkConsolePostConnectCallback,
                                           .message_received_callback = NetworkConsoleMessageReceivedCallback});
        network_console.Init();
        network_metrics = WebSocketServer({.label = "Network Metrics",
                                           .server = server,
                                           .uri = "/metrics",
                                           .num_clients_allowed = WebSocketServer::kMaxNumClients,
                                           .send_as_binary = false,  // Network metrics are always ASCII.
                                           .post_connect_callback = nullptr,
                                           .message_received_callback = nullptr});
        network_metrics.Init();
    } else {
        CONSOLE_ERROR("ADSBeeServer::TCPServerInit", "Failed to start HTTP server: %s, remaining stack %u Bytes.",
                      esp_err_to_name(ret), uxTaskGetStackHighWaterMark(NULL));
        return false;
    }

    // xTaskCreatePinnedToCore(tcp_server_task, "tcp_server", kTCPServerTaskStackSizeBytes, NULL,
    // kTCPServerTaskPriority,
    //                         NULL, kTCPServerTaskCore);

    return server != nullptr;
}