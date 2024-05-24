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

        ADSBPacket packet;
        while (ads_bee.adsb_packet_queue.Pop(packet)) {
            uint32_t packet_buffer[ADSBPacket::kMaxPacketLenWords32];
            packet.DumpPacketBuffer(packet_buffer);

            DEBUG_PRINTF("New message: 0x%08x%08x%08x%04x RSSI=%d\r\n", packet_buffer[0], packet_buffer[1],
                         packet_buffer[2], packet_buffer[3], packet.GetRSSIDBm());
            if (packet.IsValid()) {
                ads_bee.FlashStatusLED();
                DEBUG_PRINTF("df=%d ca=%d tc=%d icao_address=0x%06x\r\n", packet.GetDownlinkFormat(),
                             packet.GetCapability(), packet.GetTypeCode(), packet.GetICAOAddress());
            } else {
                DEBUG_PRINTF("INVALID %s", packet.debug_string);
            }
        }
    }
}