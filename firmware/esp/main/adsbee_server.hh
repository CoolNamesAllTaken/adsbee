#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "data_structures.hh"
#include "transponder_packet.hh"

class ADSBeeServer {
   public:
    ADSBeeServer() {};  // Default constructor.
    bool Init();
    bool Update();

    /**
     * Ingest a RawTransponderPacket written in over Coprocessor SPI.
     * @param[in] raw_packet RawTransponderPacket to ingest.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandleRawTransponderPacket(RawTransponderPacket raw_packet);

    /**
     * Task that runs continuously to receive SPI messages.
     */
    void SPIReceiveTask();

   private:
    bool spi_receive_task_should_exit_ = false;
};

extern ADSBeeServer adsbee_server;
#endif /* ADSBEE_SERVER_HH_ */