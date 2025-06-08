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

/**
 * @file cellular_modules.h
 * @brief cbmc wrapper functions in cellular_common_portable.h.
 */

/* Include paths for public enums, structures, and macros. */
#include "cellular_common_portable.h"

#if ( CBMC_TEST_CELLULAR_MODULE_RETURN_ERROR == 1 )

    CellularError_t Cellular_ModuleInit( const CellularContext_t * pContext,
                                         void ** ppModuleContext )
    {
        CellularError_t ret = nondet_int();

        __CPROVER_assume( ret >= CELLULAR_SUCCESS && ret <= CELLULAR_UNKNOWN );
        return ret;
    }

    CellularError_t Cellular_ModuleCleanUp( const CellularContext_t * pContext )
    {
        CellularError_t ret = nondet_int();

        __CPROVER_assume( ret >= CELLULAR_SUCCESS && ret <= CELLULAR_UNKNOWN );
        return ret;
    }

    CellularError_t Cellular_ModuleEnableUE( CellularContext_t * pContext )
    {
        CellularError_t ret = nondet_int();

        __CPROVER_assume( ret >= CELLULAR_SUCCESS && ret <= CELLULAR_UNKNOWN );
        return ret;
    }

    CellularError_t Cellular_ModuleEnableUrc( CellularContext_t * pContext )
    {
        CellularError_t ret = nondet_int();

        __CPROVER_assume( ret >= CELLULAR_SUCCESS && ret <= CELLULAR_UNKNOWN );
        return ret;
    }

#else /* #if ( CBMC_TEST_CELLULAR_MODULE_NO_ERROR == 1 ) */

    CellularError_t Cellular_ModuleInit( const CellularContext_t * pContext,
                                         void ** ppModuleContext )
    {
        return CELLULAR_SUCCESS;
    }

    CellularError_t Cellular_ModuleCleanUp( const CellularContext_t * pContext )
    {
        return CELLULAR_SUCCESS;
    }

    CellularError_t Cellular_ModuleEnableUE( CellularContext_t * pContext )
    {
        return CELLULAR_SUCCESS;
    }

    CellularError_t Cellular_ModuleEnableUrc( CellularContext_t * pContext )
    {
        return CELLULAR_SUCCESS;
    }

#endif /* #if ( CBMC_TEST_CELLULAR_MODULE_NO_ERROR == 1 ) */

/* ========================================================================== */
