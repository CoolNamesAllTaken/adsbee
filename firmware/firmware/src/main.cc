#include <stdio.h>

#include "pico/stdlib.h"
// #include "hardware/gpio.h"
// #include "hardware/pio.h"
// #include "hardware/clocks.h"
// // #include "hardware/dma.h"
// #include "hardware/irq.h"
// #include "blink.pio.h"
// #include "capture.pio.h"
#include "ads_b_packet.hh"
#include "ads_bee.hh"
#include "comms.hh"
#include "hal.hh"
#include "pico/binary_info.h"

ADSBee::ADSBeeConfig ads_bee_config;
// Override default config params here.
ADSBee ads_bee = ADSBee(ads_bee_config);
CommsManager comms_manager = CommsManager({});

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    stdio_init_all();

    ads_bee.Init();
    comms_manager.Init();

    while (true) {
        // Loop forever.
        comms_manager.Update();
        ads_bee.Update();

        TransponderPacket packet;
        while (ads_bee.transponder_packet_queue.Pop(packet)) {
            uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];
            packet.DumpPacketBuffer(packet_buffer);
            if (packet.GetPacketBufferLenBits() == TransponderPacket::kExtendedSquitterPacketLenBits) {
                DEBUG_PRINTF("New message: 0x%08x|%08x|%08x|%04x RSSI=%d\r\n", packet_buffer[0], packet_buffer[1],
                             packet_buffer[2], packet_buffer[3], packet.GetRSSIDBm());
            } else {
                DEBUG_PRINTF("New message: 0x%08x|%06x RSSI=%d\r\n", packet_buffer[0], packet_buffer[1],
                             packet.GetRSSIDBm());
            }

            if (packet.IsValid()) {
                ads_bee.FlashStatusLED();
                DEBUG_PRINTF("\tdf=%d icao_address=0x%06x\r\n", packet.GetDownlinkFormat(), packet.GetICAOAddress());
                ads_bee.aircraft_dictionary.IngestADSBPacket(ADSBPacket(packet));
                DEBUG_PRINTF("\taircraft_dictionary: %d aircraft\r\n", ads_bee.aircraft_dictionary.GetNumAircraft());
            } else if (packet.GetPacketBufferLenBits() == TransponderPacket::kSquitterPacketNumBits) {
                // Marked invalid because CRC could not be confirmed. See if it's in the ICAO dictionary!
                if (ads_bee.aircraft_dictionary.ContainsAircraft(packet.GetICAOAddress())) {
                    ads_bee.FlashStatusLED();
                    DEBUG_PRINTF("\tMLAT OK\r\n");
                }
                DEBUG_PRINTF("INVALID %s", packet.debug_string);
            }
        }
    }
}