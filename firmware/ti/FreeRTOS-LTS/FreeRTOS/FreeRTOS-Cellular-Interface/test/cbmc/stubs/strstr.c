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
 * @file strstr.c
 * @brief Creates a stub for strstr. This stub checks if, for the input copy
 * length, the destination and source are valid accessible memory.
 */

#include <string.h>

char * strstr( const char * s1,
               const char * s2 )
{
    size_t offset = nondet_size_t();

    __CPROVER_assert( __CPROVER_w_ok( s1, strlen( s1 ) ), "s1 write" );
    __CPROVER_assert( __CPROVER_r_ok( s1, strlen( s1 ) ), "s1 read" );

    __CPROVER_assert( __CPROVER_w_ok( s2, strlen( s2 ) ), "s2 write" );
    __CPROVER_assert( __CPROVER_r_ok( s2, strlen( s2 ) ), "s2 read" );

    if( ( offset >= 0 ) && ( offset < strlen( s1 ) ) )
    {
        return s1 + offset;
    }

    return NULL;
}
