#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "aircraft_dictionary.hh"
#include "data_structures.hh"
#include "esp_http_server.h"
#include "transponder_packet.hh"
#include "websocket_server.hh"

class ADSBeeServer {
   public:
    static const uint16_t kMaxNumTransponderPackets = 100;  // Depth of queue for incoming packets from RP2040.
    static const uint32_t kAircraftDictionaryUpdateIntervalMs = 1000;
    static const uint32_t kGDL90ReportingIntervalMs = 1000;

    static const uint16_t kNetworkConsoleQueueLen = 10;

    /**
     * Data structure used to pass netowrk console messages between threads (SPI <-> WebSocket server). Needs to be
     * manually destroyed when it's popped out of the network console packet queue.
     */
    struct NetworkConsoleMessage {
        char* buf = nullptr;
        uint16_t buf_len = 0;

        /**
         * Default constructor.
         */
        NetworkConsoleMessage() {}

        /**
         * Constructor for ingesting a pre-existing buffer. Allocates new memory and copies over the buffer contents.
         */
        NetworkConsoleMessage(const char* buf_in, uint16_t buf_in_len) : buf_len(buf_in_len) {
            buf = (char*)heap_caps_malloc(buf_len + 1, MALLOC_CAP_DMA);  // Leave room for extra null terminator.
            buf[buf_len] = '\0';                                         // Null terminate for safety.
            memcpy(buf, buf_in, buf_len);
        }

        void Destroy() { heap_caps_free(buf); }
    };

    /**
     * Constructor.
     */
    ADSBeeServer() {
        network_console_rx_queue = xQueueCreate(kNetworkConsoleQueueLen, sizeof(NetworkConsoleMessage));
        network_console_tx_queue = xQueueCreate(kNetworkConsoleQueueLen, sizeof(NetworkConsoleMessage));
        rp2040_aircraft_dictionary_metrics_queue = xQueueCreate(1, sizeof(AircraftDictionary::Metrics));
    };

    /**
     * Destructor.
     */
    ~ADSBeeServer() {
        vQueueDelete(network_console_rx_queue);
        vQueueDelete(network_console_tx_queue);
        vQueueDelete(rp2040_aircraft_dictionary_metrics_queue);
    }

    bool Init();
    bool Update();

    /**
     * Ingest a Raw1090Packet written in over Coprocessor SPI.
     * @param[in] raw_packet Raw1090Packet to ingest.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandleRaw1090Packet(Raw1090Packet& raw_packet);

    /**
     * Task that runs continuously to receive SPI messages.
     */
    void SPIReceiveTask();

    /**
     * TCP server that accepts incoming connections (used for network control via port 3333).
     */
    void TCPServerTask(void* pvParameters);

    PFBQueue<Raw1090Packet> raw_transponder_packet_queue = PFBQueue<Raw1090Packet>(
        {.buf_len_num_elements = kMaxNumTransponderPackets, .buffer = raw_transponder_packet_queue_buffer_});

    AircraftDictionary aircraft_dictionary;

    QueueHandle_t network_console_rx_queue;
    QueueHandle_t network_console_tx_queue;
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
    Raw1090Packet raw_transponder_packet_queue_buffer_[kMaxNumTransponderPackets];
    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;

    uint32_t last_gdl90_report_timestamp_ms_ = 0;
};

extern ADSBeeServer adsbee_server;
#endif /* ADSBEE_SERVER_HH_ */