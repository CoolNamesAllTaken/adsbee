#include "spi_coprocessor.hh"
#include "buffer_utils.hh"

bool SPICoprocessor::SCMessage::IsValid(uint32_t received_length)
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

void SPICoprocessor::SCMessage::PopulateCRCAndLength(uint32_t payload_length)
{
    length = payload_length + sizeof(SCMessage);
    // CRC calculation starts after the CRC itself.
    crc = calculate_crc16((uint8_t *)(&length), payload_length + sizeof(SCMessage) - sizeof(crc));
}

/** SCMessage Constructors **/

SPICoprocessor::SettingsMessage::SettingsMessage(const SettingsManager::Settings &settings_in)
{
    type = kSCPacketTypeSettings;
    settings = settings_in;
    PopulateCRCAndLength(sizeof(SettingsMessage) - sizeof(SCMessage));
}

SPICoprocessor::AircraftListMessage::AircraftListMessage(uint16_t num_aicraft_in, const Aircraft aircraft_list_in[])
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
    PopulateCRCAndLength(sizeof(AircraftListMessage) - sizeof(SCMessage));
}

SPICoprocessor::TransponderPacketMessage::TransponderPacketMessage(const TransponderPacket &packet_in)
{
    packet = packet_in;
    PopulateCRCAndLength(sizeof(TransponderPacketMessage) - sizeof(SCMessage));
}

bool SPICoprocessor::Init()
{
    bool ret = 0;
    ret &= SPIInit();
    return ret;
}

bool SPICoprocessor::Update()
{
    return true;
}

bool SPICoprocessor::SendMessage(const SCMessage &message)
{

    return true;
}

bool SPICoprocessor::SPIInit()
{
#ifdef ON_PICO
    spi_init(config_.spi_handle, config_.clk_rate_hz);
    spi_set_format(config_.spi_handle,
                   8,          // Bits per transfer.
                   SPI_CPOL_1, // Polarity (CPOL).
                   SPI_CPHA_1, // Phase (CPHA).
                   SPI_MSB_FIRST);
#else

#endif
    return true;
}

int SPICoprocessor::SPIWriteBlocking(uint8_t *tx_buf, uint32_t length)
{
#ifdef ON_PICO
    return spi_write_blocking(config_.spi_handle, tx_buf, length);
#else

#endif
    return -1;
}

int SPICoprocessor::SPIReadBlocking(uint8_t *rx_buf, uint32_t length)
{
#ifdef ON_PICO
    return spi_read_blocking(config_.spi_handle, 0, rx_buf, length);
#else

#endif
    return -1;
}