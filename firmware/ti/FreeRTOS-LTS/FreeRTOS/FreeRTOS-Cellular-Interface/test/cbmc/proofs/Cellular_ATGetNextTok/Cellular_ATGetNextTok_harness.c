/*
 * FreeRTOS-Cellular-Interface v1.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/* Standard includes. */
#include <stdint.h>

/* Cellular default config includes. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Cellular APIs includes. */
#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_common_internal.h"
#include "cellular_common_api.h"

#define ensure_memory_is_valid( px, length )    ( px != NULL ) && ( length > 0 ) && __CPROVER_w_ok( ( px ), length ) && __CPROVER_r_ok( ( px ), length )

/* Extern the com interface in comm_if_windows.c */
extern CellularCommInterface_t CellularCommInterface;

/****************************************************************
* The signature of the function under test.
****************************************************************/

CellularATError_t Cellular_ATGetNextTok( char ** ppString,
                                         char ** ppTokOutput );

/****************************************************************
* The proof of Cellular_ATGetNextTok
****************************************************************/
void harness()
{
    const char ** ppString;
    const char ** ppTokOutput;

    ppString = ( char * ) safeMalloc( sizeof( *ppString ) );
    ppTokOutput = ( char * ) safeMalloc( sizeof( *ppTokOutput ) );
    Cellular_ATGetNextTok( ppString, ppTokOutput );
}
