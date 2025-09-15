#pragma once

#include "aircraft_dictionary.hh"
#include "data_structures.hh"
#include "esp_http_server.h"
#include "websocket_server.hh"

class ADSBeeServer {
   public:
    static const uint16_t kMaxNumModeSPackets = 100;    // Depth of queue for incoming packets from RP2040.
    static const uint16_t kMaxNumUATADSBPackets = 20;   // Depth of queue for incoming UAT ADS-B packets from RP2040.
    static const uint16_t kMaxNumUATUplinkPackets = 2;  // Depth of queue for incoming UAT uplink packets from RP2040.
    static const uint32_t kAircraftDictionaryUpdateIntervalMs = 1000;
    static const uint32_t kGDL90ReportingIntervalMs = 1000;

    static const uint16_t kNetworkConsoleQueueLen = 10;

    /**
     * Constructor.
     */
    ADSBeeServer() { rp2040_aircraft_dictionary_metrics_queue = xQueueCreate(1, sizeof(AircraftDictionary::Metrics)); };

    /**
     * Destructor.
     */
    ~ADSBeeServer() { vQueueDelete(rp2040_aircraft_dictionary_metrics_queue); }

    bool Init();
    bool Update();

    /**
     * Ingest a RawModeSPacket written in over Coprocessor SPI.
     * @param[in] raw_packet RawModeSPacket to ingest.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandleRawModeSPacket(RawModeSPacket& raw_packet);
    bool HandleRawUATADSBPacket(RawUATADSBPacket& raw_packet);
    bool HandleRawUATUplinkPacket(RawUATUplinkPacket& raw_packet);

    /**
     * Task that runs continuously to receive SPI messages.
     */
    void SPIReceiveTask();

    /**
     * TCP server that accepts incoming connections (used for network control via port 3333).
     */
    void TCPServerTask(void* pvParameters);

    PFBQueue<RawModeSPacket> raw_mode_s_packet_queue = PFBQueue<RawModeSPacket>(
        {.buf_len_num_elements = kMaxNumModeSPackets, .buffer = raw_transponder_packet_queue_buffer_});
    PFBQueue<RawUATADSBPacket> raw_uat_adsb_packet_queue = PFBQueue<RawUATADSBPacket>(
        {.buf_len_num_elements = kMaxNumUATADSBPackets, .buffer = raw_uat_adsb_packet_queue_buffer_});
    PFBQueue<RawUATUplinkPacket> raw_uat_uplink_packet_queue = PFBQueue<RawUATUplinkPacket>(
        {.buf_len_num_elements = kMaxNumUATUplinkPackets, .buffer = raw_uat_uplink_packet_queue_buffer_});

    AircraftDictionary aircraft_dictionary;

    httpd_handle_t server = nullptr;
    WebSocketServer network_console;
    WebSocketServer network_metrics;

    QueueHandle_t rp2040_aircraft_dictionary_metrics_queue = nullptr;
    AircraftDictionary::Metrics rp2040_aircraft_dictionary_metrics;

   private:
    struct WSClientInfo {
        bool in_use = false;
        int client_fd = 0;
        uint32_t last_message_timestamp_ms = 0;
    };

    bool ReportGDL90();

    /**
     * Sets up the TCPServerTask as well as the WebSocket handlers and HTTP server.
     */
    bool TCPServerInit();

    bool spi_receive_task_should_exit_ = false;

    // Queue for raw packets from RP2040.
    RawModeSPacket raw_transponder_packet_queue_buffer_[kMaxNumModeSPackets];
    RawUATADSBPacket raw_uat_adsb_packet_queue_buffer_[kMaxNumUATADSBPackets];
    RawUATUplinkPacket raw_uat_uplink_packet_queue_buffer_[kMaxNumUATUplinkPackets];
    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;

    uint32_t last_gdl90_report_timestamp_ms_ = 0;
};

extern ADSBeeServer adsbee_server;