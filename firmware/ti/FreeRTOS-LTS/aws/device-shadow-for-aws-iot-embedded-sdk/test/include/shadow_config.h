/*
 * AWS IoT Device Shadow v1.4.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file shadow_config.h
 * @brief Config values for testing the AWS IoT Device Shadow Library.
 */

#ifndef SHADOW_CONFIG_H_
#define SHADOW_CONFIG_H_

#include <stdio.h>

#ifdef DISABLE_LOGGING
    #ifndef LogError
        #define LogError( message )
    #endif
    #ifndef LogWarn
        #define LogWarn( message )
    #endif

    #ifndef LogInfo
        #define LogInfo( message )
    #endif

    #ifndef LogDebug
        #define LogDebug( message )
    #endif
#else /* ! DISABLE_LOGGING */
    #define LogError( message )    printf( "Error: " ); printf message; printf( "\n" )

    #define LogWarn( message )     printf( "Warn: " ); printf message; printf( "\n" )

    #define LogInfo( message )     printf( "Info: " ); printf message; printf( "\n" )

    #define LogDebug( message )    printf( "Debug: " ); printf message; printf( "\n" )
#endif /* DISABLE_LOGGING */

#endif /* ifndef SHADOW_CONFIG_H_ */
