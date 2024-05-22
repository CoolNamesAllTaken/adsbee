#include <stdio.h>

#include "pico/stdlib.h"
// #include "hardware/gpio.h"
// #include "hardware/pio.h"
// #include "hardware/clocks.h"
// // #include "hardware/dma.h"
// #include "hardware/irq.h"
// #include "blink.pio.h"
// #include "capture.pio.h"
#include "comms.hh"
#include "hal.hh"
#include "main.hh"
#include "pico/binary_info.h"

ADSBee::ADSBeeConfig ads_bee_config;
// Override default config params here.
ADSBee ads_bee = ADSBee(ads_bee_config);
CommsManager comms_manager = CommsManager({.ads_bee = ads_bee});

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    stdio_init_all();

    ads_bee.Init();
    comms_manager.Init();

    while (true) {
        // Loop forever.
        comms_manager.Update();
        ads_bee.Update();
    }
}