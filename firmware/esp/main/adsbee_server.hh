#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "aircraft_dictionary.hh"
#include "data_structures.hh"
#include "transponder_packet.hh"

class ADSBeeServer {
   public:
    static const uint16_t kMaxNumTransponderPackets = 100;  // Depth of queue for incoming packets from RP2040.
    static const uint32_t kAircraftDictionaryUpdateIntervalMs = 1000;
    static const uint32_t kGDL90ReportingIntervalMs = 1000;

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

    PFBQueue<RawTransponderPacket> transponder_packet_queue = PFBQueue<RawTransponderPacket>(
        {.buf_len_num_elements = kMaxNumTransponderPackets, .buffer = transponder_packet_queue_buffer_});

    AircraftDictionary aircraft_dictionary;

   private:
    bool ReportGDL90();

    bool TCPServerInit();

    bool spi_receive_task_should_exit_ = false;

    RawTransponderPacket transponder_packet_queue_buffer_[kMaxNumTransponderPackets];
    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;

    uint32_t last_gdl90_report_timestamp_ms_ = 0;
};

extern ADSBeeServer adsbee_server;
#endif /* ADSBEE_SERVER_HH_ */