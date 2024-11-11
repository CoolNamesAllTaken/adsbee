#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "aircraft_dictionary.hh"
#include "data_structures.hh"
#include "esp_http_server.h"
#include "transponder_packet.hh"

class ADSBeeServer {
   public:
    static const uint16_t kMaxNumTransponderPackets = 100;  // Depth of queue for incoming packets from RP2040.
    static const uint32_t kAircraftDictionaryUpdateIntervalMs = 1000;
    static const uint32_t kGDL90ReportingIntervalMs = 1000;

    static const uint16_t kNetworkConsoleQueueLen = 10;
    static const uint16_t kNetworkConsoleMaxNumClients = 3;
    static const uint32_t kNetworkConsoleInactivityTimeoutMs =
        10 * 60e3;  // Time without a message before a network console client is disconnected.

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
            buf = (char*)malloc(buf_len + 1);  // Leave room for extra null terminator.
            buf[buf_len] = '\0';               // Null terminate for safety.
            memcpy(buf, buf_in, buf_len);
        }

        void Destroy() { free(buf); }
    };

    ADSBeeServer() {};  // Default constructor.
    bool Init();
    bool Update();

    /**
     * Ingest a RawTransponderPacket written in over Coprocessor SPI.
     * @param[in] raw_packet RawTransponderPacket to ingest.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandleRawTransponderPacket(RawTransponderPacket& raw_packet);

    /**
     * Task that runs continuously to receive SPI messages.
     */
    void SPIReceiveTask();

    /**
     * TCP server that accepts incoming connections (used for network control via port 3333).
     */
    void TCPServerTask(void* pvParameters);

    /**
     * Add a new client connection for the Network Console WebSocket.
     * @param[in] client_fd File descriptor for writing to the client.
     * @retval True if client was successfully added, false if maximum number of clients already reached.
     */
    bool NetworkConsoleAddWebSocketClient(int client_fd);

    /**
     * Remove a client connection from the Network Console WebSocket.
     * @param[in] client_fd File descriptor for the client to remove.
     * @retval True if client was successfully removed, false if client wasn't found in the connectin list.
     */
    bool NetworkConsoleRemoveWebsocketClient(int client_fd);

    void NetworkConsoleBroadcastMessage(const char* message);
    esp_err_t NetworkConsoleSendMessage(int client_fd, const char* message);
    bool NetworkConsoleUpdateActivityTimer(int client_fd);

    /**
     * Handler for incoming websocket connections to the network console.
     */
    esp_err_t NetworkConsoleWebSocketHandler(httpd_req_t* req);

    PFBQueue<RawTransponderPacket> transponder_packet_queue = PFBQueue<RawTransponderPacket>(
        {.buf_len_num_elements = kMaxNumTransponderPackets, .buffer = transponder_packet_queue_buffer_});

    AircraftDictionary aircraft_dictionary;

    QueueHandle_t network_console_rx_queue;
    QueueHandle_t network_console_tx_queue;
    httpd_handle_t server = nullptr;

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

    RawTransponderPacket transponder_packet_queue_buffer_[kMaxNumTransponderPackets];
    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;

    uint32_t last_gdl90_report_timestamp_ms_ = 0;

    WSClientInfo network_console_clients[kNetworkConsoleMaxNumClients] = {0};
};

extern ADSBeeServer adsbee_server;
#endif /* ADSBEE_SERVER_HH_ */