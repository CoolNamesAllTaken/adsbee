/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Driver code:
 * Copyright (C) Nicholas J. Kinar <n.kinar@usask.ca>, Centre for Hydrology, University of Saskatchewan
 *
 * MSP432 Driverlib (C) 2017-2019 Texas Instruments Incorporated <https://www.ti.com/>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#pragma once
#include <stdint.h>
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "semphr.h"

#define MAX_NAME_LLMNR    32 /* maximum length of the LLMNR name used in this project */

struct InternalNetworkMiddlewareData
{
    uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ];
    uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    BaseType_t resetNetworkTaskRunning;
    uint32_t resetNetworkTaskEveryXSeconds;
    char deviceName[ MAX_NAME_LLMNR ];
}; /* end */

void vPublicSetupFreeRTOSTasks( const struct InternalNetworkMiddlewareData data );
void vPublicSetupDeviceName( const char * deviceName );
BaseType_t vPublicPreventNetworkReset( const BaseType_t preventReset,
                                       const uint32_t waitTime );
void vConvertOctetsToAddr( uint8_t arr[ ipIP_ADDRESS_LENGTH_BYTES ],
                           uint8_t b0,
                           uint8_t b1,
                           uint8_t b2,
                           uint8_t b3 );
