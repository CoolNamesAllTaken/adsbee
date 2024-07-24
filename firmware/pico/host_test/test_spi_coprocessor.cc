#include "gtest/gtest.h"
#include "spi_coprocessor.hh"

TEST(SPICoprocessor, CreateSCpacket) {
    SPICoprocessor::SCMessage packet = {.crc = 0x1234, .length = 0};
    EXPECT_FALSE(packet.IsValid(sizeof(SPICoprocessor::SCMessage)));

    packet.PopulateCRCAndLength(0);
    EXPECT_TRUE(packet.IsValid(sizeof(SPICoprocessor::SCMessage)));
}

TEST(SPICoprocessor, CreateSettingsPacket) {
    SettingsManager::Settings settings = {
        .rx_gain = 15, .comms_uart_baud_rate = 12345, .wifi_enabled = true, .wifi_password = "helloooo"};

    SPICoprocessor::SettingsMessage packet = SPICoprocessor::SettingsMessage(settings);
    EXPECT_TRUE(packet.IsValid(sizeof(SPICoprocessor::SettingsMessage)));
    EXPECT_EQ(settings.rx_gain, packet.settings.rx_gain);
    EXPECT_EQ(settings.comms_uart_baud_rate, packet.settings.comms_uart_baud_rate);
    EXPECT_EQ(settings.wifi_enabled, packet.settings.wifi_enabled);
    EXPECT_STREQ(settings.wifi_password, packet.settings.wifi_password);
    EXPECT_EQ(packet.type, SPICoprocessor::kSCPacketTypeSettings);

    packet.settings.comms_uart_baud_rate |= 0x123;  // Corrupt the packet.
    EXPECT_FALSE(packet.IsValid(sizeof(SPICoprocessor::SettingsMessage)));
}

TEST(SPICoprocessor, CreateAircraftListPacket) {
    Aircraft aircraft_list[AircraftDictionary::kMaxNumAircraft];
    aircraft_list[0].icao_address = 0x12345;
    aircraft_list[1].heading_deg = 3;
    aircraft_list[99].icao_address = 0xBEEF;
    uint16_t num_aircraft = 100;
    SPICoprocessor::AircraftListMessage packet = SPICoprocessor::AircraftListMessage(num_aircraft, aircraft_list);
    EXPECT_TRUE(packet.IsValid(sizeof(SPICoprocessor::AircraftListMessage)));
    EXPECT_EQ(aircraft_list[0].icao_address, packet.aircraft_list[0].icao_address);
    EXPECT_EQ(aircraft_list[1].heading_deg, packet.aircraft_list[1].heading_deg);
    EXPECT_EQ(aircraft_list[99].icao_address, packet.aircraft_list[99].icao_address);
    EXPECT_EQ(num_aircraft, packet.num_aicraft);
    EXPECT_EQ(packet.type, SPICoprocessor::kSCPacketTypeAircraftList);

    packet.aircraft_list[0].icao_address = 0;  // Corrupt the packet.
    EXPECT_FALSE(packet.IsValid(sizeof(SPICoprocessor::AircraftListMessage)));
}