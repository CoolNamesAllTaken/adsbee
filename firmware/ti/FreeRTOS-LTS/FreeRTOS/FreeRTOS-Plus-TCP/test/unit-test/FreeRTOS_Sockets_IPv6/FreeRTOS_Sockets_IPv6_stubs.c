/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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


/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* ===========================  EXTERN VARIABLES  =========================== */

volatile BaseType_t xInsideInterrupt = pdFALSE;

QueueHandle_t xNetworkEventQueue = NULL;

/* ======================== Stub Callback Functions ========================= */

void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}

/**
 * @brief Convert an ASCII character to its corresponding hexadecimal value.
 *        Accepted characters are 0-9, a-f, and A-F.
 *
 * @param[in] cChar The character to be converted.
 *
 * @return The hexadecimal value, between 0 and 15.
 *         When the character is not valid, socketINVALID_HEX_CHAR will be returned.
 */

uint8_t ucASCIIToHex( char cChar )
{
    char cValue = cChar;
    uint8_t ucNew;

    if( ( cValue >= '0' ) && ( cValue <= '9' ) )
    {
        cValue -= ( char ) '0';
        /* The value will be between 0 and 9. */
        ucNew = ( uint8_t ) cValue;
    }
    else if( ( cValue >= 'a' ) && ( cValue <= 'f' ) )
    {
        cValue -= ( char ) 'a';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else if( ( cValue >= 'A' ) && ( cValue <= 'F' ) )
    {
        cValue -= ( char ) 'A';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else
    {
        /* The character does not represent a valid hex number, return 255. */
        ucNew = ( uint8_t ) socketINVALID_HEX_CHAR;
    }

    return ucNew;
}
