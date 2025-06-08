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
 * @file strchr.c
 * @brief Creates a stub for strchr. This stub checks if, for the input copy
 * length, the destination and source are valid accessible memory.
 */

#include <string.h>

/* This is a clang macro not available on linux */
#ifndef __has_builtin
    #define __has_builtin( x )    0
#endif

#if __has_builtin( __builtin___strchr )
    char * __builtin___strchr_chk( const char * s,
                                   int c )
    {
        if( __CPROVER_w_ok( s, 1 ) && __CPROVER_r_ok( s, 1 ) )
        {
            while( *s != '\0' )
            {
                if( ( int ) *s == c )
                {
                    return s;
                }

                if( __CPROVER_w_ok( s + 1, 1 ) && __CPROVER_r_ok( s + 1, 1 ) )
                {
                    s++;
                }
            }

            return NULL;
        }
    }
#else /* if __has_builtin( __builtin___strchr ) */
    char * strchr( const char * s,
                   int c )
    {
        if( __CPROVER_w_ok( s, 1 ) && __CPROVER_r_ok( s, 1 ) )
        {
            while( *s != '\0' )
            {
                if( ( int ) *s == c )
                {
                    return s;
                }

                if( __CPROVER_w_ok( s + 1, 1 ) && __CPROVER_r_ok( s + 1, 1 ) )
                {
                    s++;
                }
            }

            return NULL;
        }
    }
#endif /* if __has_builtin( __builtin___strchr ) */
