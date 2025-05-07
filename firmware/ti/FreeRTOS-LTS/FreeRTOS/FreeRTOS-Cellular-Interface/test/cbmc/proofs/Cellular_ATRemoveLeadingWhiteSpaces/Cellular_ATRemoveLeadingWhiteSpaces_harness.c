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

CellularATError_t Cellular_ATRemoveLeadingWhiteSpaces( char ** ppString );

/****************************************************************
* The proof of Cellular_ATRemoveLeadingWhiteSpaces
****************************************************************/
void harness()
{
    uint16_t stringLength;

    __CPROVER_assume( stringLength < CBMC_MAX_BUFSIZE );
    __CPROVER_assume( stringLength > 0 );
    char * pString = ( char * ) safeMalloc( stringLength );
    char ** ppString = nondet_bool() ? NULL : &pString;

    if( ( pString == NULL ) || ( ( pString != NULL ) && ensure_memory_is_valid( pString, stringLength ) ) )
    {
        if( pString != NULL )
        {
            pString[ stringLength - 1 ] = '\0';
        }

        Cellular_ATRemoveLeadingWhiteSpaces( ppString );
    }
}
