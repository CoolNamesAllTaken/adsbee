#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "adsb_packet.hh"
#include "aircraft_dictionary.hh"
#include "settings.hh"

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
        uint16_t crc16;  // 16-bit CRC of all bytes after the CRC.
        uint32_t length; // Length of the packet in bytes.
        SPICoprocessor::PacketType type;
    };

    struct SettingsPacket : public SCPacket
    {
        SettingsManager::Settings settings;
    };

    struct AircraftListPacket : public SCPacket
    {
        uint16_t num_aicraft;
        Aircraft aircraft_list[];
    };
};

#endif /* SPI_COPROCESSOR_HH_ */