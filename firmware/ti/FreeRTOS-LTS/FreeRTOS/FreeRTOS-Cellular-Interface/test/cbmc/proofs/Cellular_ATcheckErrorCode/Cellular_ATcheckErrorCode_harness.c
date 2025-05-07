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

CellularATError_t Cellular_ATcheckErrorCode( const char * pInputBuf,
                                             const char * const * const ppKeyList,
                                             size_t keyListLen,
                                             bool * pResult );

/****************************************************************
* The proof of Cellular_ATcheckErrorCode
****************************************************************/
void harness()
{
    uint16_t stringLen;
    uint16_t keyListLen;

    __CPROVER_assume( stringLen < CBMC_MAX_BUFSIZE );
    __CPROVER_assume( stringLen > 0 );
    __CPROVER_assume( keyListLen < KEY_LIST_SIZE );
    char * pInputBuf = ( char * ) safeMalloc( stringLen );
    bool * pResult = ( uint8_t * ) safeMalloc( sizeof( bool * ) );
    char ** ppKeyList = ( char ** ) safeMalloc( sizeof( char ** ) * keyListLen );

    if( ( pInputBuf == NULL ) || ( ( pInputBuf != NULL ) && ensure_memory_is_valid( pInputBuf, stringLen ) ) )
    {
        if( pInputBuf != NULL )
        {
            pInputBuf[ stringLen - 1 ] = '\0';
        }

        Cellular_ATcheckErrorCode( pInputBuf,
                                   ppKeyList,
                                   keyListLen,
                                   pResult );
    }
}
