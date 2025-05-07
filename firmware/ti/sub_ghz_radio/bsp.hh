#pragma once

#include <ti/drivers/GPIO.h>
#include "stdint.h"

class BSP
{
public:
    static const uint_least8_t kStatusLEDPin = 7;
};

extern BSP bsp;