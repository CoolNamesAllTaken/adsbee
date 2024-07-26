#include "spi_coprocessor.hh"
#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hardware/gpio.h"
#else
#endif

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

// SPICoprocessor::DecodedTransponderPacketMessage::DecodedTransponderPacketMessage(const DecodedTransponderPacket &packet_in)
// {
//     packet = packet_in;
//     PopulateCRCAndLength(sizeof(DecodedTransponderPacketMessage) - sizeof(SCMessage));
// }

bool SPICoprocessor::Init()
{
    bool ret = true;
    ret &= SPIInit();
    return ret;
}

bool SPICoprocessor::DeInit()
{
    bool ret = true;
    ret &= SPIDeInit();
    return ret;
}

bool SPICoprocessor::Update()
{
    return true;
}

bool SPICoprocessor::SendMessage(SCMessage &message)
{
#ifdef ON_PICO
    gpio_put(config_.spi_cs_pin, 0);
    uint8_t *tx_buf = reinterpret_cast<uint8_t *>(&message);
    spi_write_blocking(config_.spi_handle, tx_buf, message.length);
    gpio_put(config_.spi_cs_pin, 1);
#else
#endif
    return true;
}

bool SPICoprocessor::SPIInit()
{
#ifdef ON_PICO
    // ESP32 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // ESP32 handshake pin.
    gpio_init(config_.spi_handshake_pin);
    gpio_set_dir(config_.spi_handshake_pin, GPIO_IN);
    gpio_set_pulls(config_.spi_handshake_pin, true, false); // Handshake pin is pulled up.
    // ESP32 SPI pins.
    gpio_set_function(config_.spi_clk_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_mosi_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_miso_pin, GPIO_FUNC_SPI);

    // Initialize SPI Peripheral.
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

bool SPICoprocessor::SPIDeInit()
{
#ifdef ON_PICO
    // ESP32 chip select pin.
    gpio_deinit(config_.spi_cs_pin);
    // ESP32 handshake pin.
    gpio_deinit(config_.spi_handshake_pin);

    // De-initialize SPI Peripheral.
    spi_deinit(config_.spi_handle);
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