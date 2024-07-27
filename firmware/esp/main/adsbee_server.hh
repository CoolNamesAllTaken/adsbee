#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "data_structures.hh"
#include "settings.hh"
#include "spi_coprocessor.hh"

class ADSBeeServer
{
public:
    ADSBeeServer();
    bool Init();
    bool Update();

    bool IngestSPIPacket(uint8_t *buf, uint16_t buf_len_bytes);
};
#endif /* ADSBEE_SERVER_HH_ */