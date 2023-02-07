#include <stdio.h>
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "pico/binary_info.h"
#include "scbs.hh"


SCBS * scbs = NULL;

int main() {
    bi_decl(bi_program_description("SCBS-Pico Single Cell Battery Simulator"));
    // bi_decl(bi_1pin_with_name(LED_PIN, "On-board LED"));

    stdio_init_all();

    SCBS::SCBSConfig_t scbs_config;
    scbs = new SCBS(scbs_config);
    scbs->Init();

    while (true) {
        scbs->Update();
    }
}