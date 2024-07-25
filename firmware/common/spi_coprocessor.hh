#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "adsb_packet.hh"
#include "aircraft_dictionary.hh"
#include "settings.hh"

#ifdef ON_PICO
#include "hardware/spi.h"
#else
// TODO: Include ESP32 SPI header.
#endif

class SPICoprocessor
{
public:
    struct SPICoprocessorConfig
    {
        uint32_t clk_rate_hz = 40e6; // 40 MHz
#ifdef ON_PICO
        spi_inst_t *spi_handle = spi1;
        uint16_t spi_clk_pin = 10;
        uint16_t spi_mosi_pin = 11;
        uint16_t spi_miso_pin = 12;
        uint16_t spi_cs_pin = 9;
        uint16_t spi_handshake_pin = 13;
#else
        // TODO: Initialize ESP32 SPI parameters here.
#endif
    };

    enum PacketType : int8_t
    {
        kSCPacketTypeInvalid = -1,
        kSCPacketTypeSettings,
        kSCPacketTypeNetworkMessage,
        kSCPacketTypeAircraftList
    };

    struct SCMessage
    {
        uint16_t crc;    // 16-bit CRC of all bytes after the CRC.
        uint32_t length; // Length of the packet in bytes.
        SPICoprocessor::PacketType type;

        /**
         * Checks to see if a SPICoprocessor packet (SCMessage) is valid.
         * @param[in] received_length Number of bytes received over SPI.
         * @retval True if packet is valid, false otherwise.
         */
        bool IsValid(uint32_t received_length);

        /**
         * Sets the packet length and CRC based on the payload. CRC is calculated for everything after the CRC itself.
         * @param[in] payload_length Number of bytes in the payload, which begins right after length for packets that
         * inherit from SCMessage.
         */
        void PopulateCRCAndLength(uint32_t payload_length);
    };

    struct SettingsMessage : public SCMessage
    {
        SettingsManager::Settings settings;

        /**
         * SettingsMessage constructor. Populates the settings and adds length, packet type, and CRC info to parent.
         * @param[in] settings Reference to a SettingsManager::Settings struct to send over.
         * @retval The constructed Settings Packet.
         */
        SettingsMessage(const SettingsManager::Settings &settings_in);
    };

    struct AircraftListMessage : public SCMessage
    {
        uint16_t num_aicraft;
        Aircraft aircraft_list[AircraftDictionary::kMaxNumAircraft];

        /**
         * AircraftListMessage constructor. Populates the aircraft list and adds length, packet type, and CRC info to
         * parent.
         * @param[in] num_aircraft Number of aircraft in the list. Determines the length of the packet.
         * @param[in] aircraft_list Array of Aircraft objects.
         * @retval The constructed AircraftListMessage.
         */
        AircraftListMessage(uint16_t num_aicraft_in, const Aircraft aircraft_list_in[]);
    };

    struct TransponderPacketMessage : public SCMessage
    {
        TransponderPacket packet;

        /**
         * TransponderPacketMessage constructor. Populates the packet to send and adds length, packet type, and CRC info
         * to parent.
         * @param[in] packet Reference to transponder packet to use for construction.
         */
        TransponderPacketMessage(const TransponderPacket &packet_in);
    };

    // NOTE: Pico (leader) and ESP32 (follower) will have different behaviors for these functions.
    bool
    Init();
    bool DeInit();
    bool Update();

    /**
     * Transmit a packet to the coprocessor. Blocking.
     * @param[in] packet Reference to the packet that will be transmitted.
     * @retval True if succeeded, false otherwise.
     */
    bool SendMessage(SCMessage &message);

private:
    bool SPIInit();
    bool SPIDeInit();
    int SPIWriteBlocking(uint8_t *tx_buf, uint32_t length);
    int SPIReadBlocking(uint8_t *rx_buf, uint32_t length);

    SPICoprocessorConfig config_;
};

#ifdef ON_PICO
extern SPICoprocessor esp32;
#else
extern SPICoprocessor pico;
#endif

#endif /* SPI_COPROCESSOR_HH_ */