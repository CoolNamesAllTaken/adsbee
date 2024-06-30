#include "spi_coprocessor.hh"
#include "buffer_utils.hh"

bool SPICoprocessor::SCPacket::IsValid(uint32_t received_length)
{
    if (received_length != length)
    {
        return false;
    }
    if (calculate_crc16((uint8_t *)&length, length - sizeof(crc)) != crc)
    {
        return false;
    }
    return true;
}

void SPICoprocessor::SCPacket::PopulateCRCAndLength(uint32_t payload_length)
{
    length = payload_length + sizeof(SCPacket);
    // CRC calculation starts after the CRC itself.
    crc = calculate_crc16((uint8_t *)(&length), payload_length + sizeof(SCPacket) - sizeof(crc));
}

/** SCPacket Constructors **/

SPICoprocessor::SettingsPacket::SettingsPacket(const SettingsManager::Settings &settings_in)
{
    type = kSCPacketTypeSettings;
    settings = settings_in;
    PopulateCRCAndLength(sizeof(SettingsPacket) - sizeof(SCPacket));
}

SPICoprocessor::AircraftListPacket::AircraftListPacket(uint16_t num_aicraft_in, const Aircraft aircraft_list_in[])
{
    type = kSCPacketTypeAircraftList;
    num_aicraft = num_aicraft_in;
    // Copy over the aircraft that we are tracking.
    for (uint16_t i = 0; i < num_aicraft; i++)
    {
        aircraft_list[i] = aircraft_list_in[i];
    }
    // Set the rest of the aircraft list to 0's.
    for (uint16_t i = num_aicraft; i < AircraftDictionary::kMaxNumAircraft; i++)
    {
        aircraft_list[i] = Aircraft();
    }
    // memset(&(aircraft_list[num_aicraft]), 0, sizeof(Aircraft) * (AircraftDictionary::kMaxNumAircraft - num_aicraft));
    PopulateCRCAndLength(sizeof(AircraftListPacket) - sizeof(SCPacket));
}
