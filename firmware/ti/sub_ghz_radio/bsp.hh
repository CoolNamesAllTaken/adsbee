#pragma once

#include <ti/drivers/GPIO.h>
#include "stdint.h"

class BSP
{
public:
    static const uint16_t kSubGLEDPin = 6;
    static const uint16_t kSyncPin = 5;
    static const uint16_t kSubGIRQPin = 18;
    static const uint16_t kSubGBiasTeeEnablePin = 7;
    static const uint16_t kCoProSPIMISOPin = 8;
    static const uint16_t kCoProSPIMOSIPin = 9;
    static const uint16_t kCoPrSPICLKPin = 10;
};

extern BSP bsp;