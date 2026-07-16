#pragma once

#include "aircraft_dictionary.hh"
#include "composite_array.hh"
#include "data_structures.hh"
#include "esp_http_server.h"
#include "websocket_server.hh"

class SensorFusion;  // Forward declared; the AHRS attitude source lives ESP-side (see SetSensorFusion).
class Spl06003;      // Forward declared; the barometer (ownship pressure altitude) lives ESP-side (see SetBarometer).

class ADSBeeServer {
   public:
    static const uint16_t kMaxNumModeSPackets = 300;    // Depth of queue for incoming packets from RP2040.
    static const uint16_t kMaxNumUATADSBPackets = 20;   // Depth of queue for incoming UAT ADS-B packets from RP2040.
    static const uint16_t kMaxNumUATUplinkPackets = 2;  // Depth of queue for incoming UAT uplink packets from RP2040.
    static const uint32_t kAircraftDictionaryUpdateIntervalMs = 1000;
    static const uint32_t kRawPacketProcessingIntervalMs = 200;
    static const uint32_t kGDL90ReportingIntervalMs = 1000;
    static const uint32_t kAHRSReportingIntervalMs = 200;  // ForeFlight AHRS message rate: 5 Hz.
    static const uint32_t kAircraftJSONReportingIntervalMs = 1000;

    static const uint16_t kNetworkConsoleQueueLen = 10;

    /**
     * Constructor.
     */
    ADSBeeServer() {
        rp2040_aircraft_dictionary_metrics_queue = xQueueCreate(1, sizeof(AircraftDictionary::Metrics));
        raw_packets_buf_ = (uint8_t*)heap_caps_malloc(CompositeArray::RawPackets::kMaxLenBytes, MALLOC_CAP_8BIT);
    };

    /**
     * Destructor.
     */
    ~ADSBeeServer() {
        vQueueDelete(rp2040_aircraft_dictionary_metrics_queue);
        if (raw_packets_buf_) {
            heap_caps_free(raw_packets_buf_);
        }
    }

    bool Init();
    bool Update();

    /**
     * Provide the sensor fusion source used to populate the ForeFlight AHRS message. Only called on boards that run
     * sensor fusion (winglet); left unset elsewhere, in which case no AHRS messages are emitted.
     */
    void SetSensorFusion(SensorFusion& sensor_fusion) { sensor_fusion_ = &sensor_fusion; }

    /**
     * Provide the barometer used to populate the GDL90 ownship report pressure altitude. Only called on boards with a
     * barometer (winglet); left unset elsewhere, in which case the ownship falls back to rx_position.baro_altitude_ft.
     */
    void SetBarometer(Spl06003& barometer) { barometer_ = &barometer; }

    /**
     * Task that runs continuously to receive SPI messages.
     */
    void SPIReceiveTask();

    /**
     * TCP server that accepts incoming connections (used for network control via port 3333).
     */
    void TCPServerTask(void* pvParameters);

    // Written by Core 1 (SPI task) and read by Core 0 (main task) — must be thread-safe.
    // Define PFB_QUEUE_NO_THREAD_SAFETY to disable mutex locking (e.g. to diagnose deadlocks).
    PFBQueue<RawModeSPacket> raw_mode_s_packet_in_queue =
        PFBQueue<RawModeSPacket>({.buf_len_num_elements = kMaxNumModeSPackets,
                                  .buffer = raw_mode_s_packet_in_queue_buffer_,
#ifndef PFB_QUEUE_NO_THREAD_SAFETY
                                  .is_thread_safe = true
#endif
        });
    PFBQueue<RawUATADSBPacket> raw_uat_adsb_packet_in_queue =
        PFBQueue<RawUATADSBPacket>({.buf_len_num_elements = kMaxNumUATADSBPackets,
                                    .buffer = raw_uat_adsb_packet_in_queue_buffer_,
#ifndef PFB_QUEUE_NO_THREAD_SAFETY
                                    .is_thread_safe = true
#endif
        });
    PFBQueue<RawUATUplinkPacket> raw_uat_uplink_packet_in_queue =
        PFBQueue<RawUATUplinkPacket>({.buf_len_num_elements = kMaxNumUATUplinkPackets,
                                      .buffer = raw_uat_uplink_packet_in_queue_buffer_,
#ifndef PFB_QUEUE_NO_THREAD_SAFETY
                                      .is_thread_safe = true
#endif
        });

    AircraftDictionary aircraft_dictionary;

    // Read-only access to the aircraft dictionary for UI rendering.
    const AircraftDictionary& GetAircraftDictionary() const { return aircraft_dictionary; }

    httpd_handle_t server = nullptr;
    WebSocketServer network_console;
    WebSocketServer network_metrics;
    WebSocketServer network_aircraft;

    QueueHandle_t rp2040_aircraft_dictionary_metrics_queue = nullptr;
    AircraftDictionary::Metrics rp2040_aircraft_dictionary_metrics;

   private:
    struct WSClientInfo {
        bool in_use = false;
        int client_fd = 0;
        uint32_t last_message_timestamp_ms = 0;
    };

    /**
     * Send a GDL90 report of all aircraft positions to connected WiFi clients.
     * @retval True if successful, false on error.
     */
    bool ReportGDL90();

    /**
     * Sends a GDL90 uplink packet to connected WiFi clients. Does not provide traffic reports.
     * @param[in] uplink_packet Decoded UAT uplink packet to send.
     * @retval True if successful, false on error.
     */
    bool ReportGDL90UplinkDataMessage(const DecodedUATUplinkPacket& uplink_packet);

    /**
     * Send a ForeFlight AHRS (attitude / heading) message to connected WiFi clients from the sensor fusion source.
     * @retval True if successful, false on error.
     */
    bool ReportGDL90AHRS();

    /**
     * Broadcasts metrics message to all connected network metrics websocket clients.
     */
    void SendNetworkMetricsMessage();

    /**
     * Broadcasts one JSON object per tracked aircraft to all connected /aircraft websocket clients.
     */
    void SendAircraftJSONMessages();

    void SetOwnshipPosition(float latitude_deg, float longitude_deg);

    /**
     * Sets up the TCPServerTask as well as the WebSocket handlers and HTTP server.
     */
    bool TCPServerInit();

    bool spi_receive_task_should_exit_ = false;

    // Queue for raw packets from RP2040.
    RawModeSPacket raw_mode_s_packet_in_queue_buffer_[kMaxNumModeSPackets];
    RawUATADSBPacket raw_uat_adsb_packet_in_queue_buffer_[kMaxNumUATADSBPackets];
    RawUATUplinkPacket raw_uat_uplink_packet_in_queue_buffer_[kMaxNumUATUplinkPackets];

    uint8_t* raw_packets_buf_ = nullptr;

    uint32_t last_raw_packet_process_timestamp_ms_ = 0;
    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;
    uint32_t last_gdl90_report_timestamp_ms_ = 0;
    uint32_t last_ahrs_report_timestamp_ms_ = 0;
    uint32_t last_aircraft_json_report_timestamp_ms_ = 0;

    // AHRS attitude source. Null unless SetSensorFusion() was called (winglet boards only).
    SensorFusion* sensor_fusion_ = nullptr;

    // Barometer for ownship pressure altitude. Null unless SetBarometer() was called (winglet boards only).
    Spl06003* barometer_ = nullptr;
};

extern ADSBeeServer adsbee_server;