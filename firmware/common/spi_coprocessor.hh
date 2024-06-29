#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "adsb_packet.hh"
#include "aircraft_dictionary.hh"

class SPICoprocessor
{
    enum PacketType : int8_t
    {
        kSCPacketTypeInvalid = -1,
        kSCPacketTypeSettings,
        kSCPacketTypeNetworkMessage,
        kSCPacketTypeAircraftList
    };

    struct SCPacket
    {
        SPICoprocessor::PacketType type;
    };

        struct AircraftListPacket : public SCPacket
    {
        uint16_t num_aicraft;
        Aircraft aircraft_list[];
    };
};

#endif /* SPI_COPROCESSOR_HH_ */