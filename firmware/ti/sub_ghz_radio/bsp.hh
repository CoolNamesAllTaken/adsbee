#pragma once

#include <ti/drivers/GPIO.h>
#include "stdint.h"
#include "ti_drivers_config.h"

class BSP
{
public:
    // Pins are retained for reference only, all initialization is done in the syscfg code.
    static const uint_least8_t kSubGLEDPin = SUBG_LED_PIN;
    static const uint_least8_t kSyncPin = SYNC_PIN;
    static const uint_least8_t kSubGIRQPin = SUBG_IRQ_PIN;
    static const uint_least8_t kSubGBiasTeeEnablePin = SUBG_BIAS_TEE_ENABLE_PIN;
    static const uint_least8_t kCoProSPIMISOPin = CONFIG_GPIO_COPRO_SPI_POCI;
    static const uint_least8_t kCoProSPIMOSIPin = CONFIG_GPIO_COPRO_SPI_PICO;
    static const uint_least8_t kCoProSPICLKPin = CONFIG_GPIO_COPRO_SPI_SCLK;
    static const uint_least8_t kCoProSPICSPin = CONFIG_GPIO_COPRO_SPI_CSN;

    // Coprocessor SPI index is used to select which SPI peripheral to use.
    static const uint_least8_t kCoProSPIIndex = COPRO_SPI;
};

extern BSP bsp;