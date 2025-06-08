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

struct InternalNetworkInterfaceMSP432EConfig
{
    BaseType_t turnOnEMAC;                           /* true to turn on the EMAC initially on startup */
    uint8_t ucMACAddr[ ipMAC_ADDRESS_LENGTH_BYTES ]; /* MAC address */
    BaseType_t setMACAddrInternal;                   /* true to set the MAC address from internal registers */
};                                                   /* end */

BaseType_t vPublicCheckNetworkInterfaceUp();
void vPublicGetMACAddr( uint8_t pui8MACAddrGet[ ipMAC_ADDRESS_LENGTH_BYTES ] );
BaseType_t vPublicSetupEMACNetwork( const struct InternalNetworkInterfaceMSP432EConfig config );
void vGetInternalNetworkInterfaceMSP432EConfigDefaults( struct InternalNetworkInterfaceMSP432EConfig * config );
