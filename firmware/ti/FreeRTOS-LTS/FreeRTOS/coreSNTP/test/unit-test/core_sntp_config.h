/*
 * coreSNTP v1.3.1
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
 */

/**
 * @file core_sntp_config.h
 * @brief This header sets configuration macros for the SNTP library.
 */
#ifndef CORE_SNTP_CONFIG_H_
#define CORE_SNTP_CONFIG_H_

/* Standard include. */
#include <stdio.h>

/* @[code_example_loggingmacros] */
/************* Define Logging Macros using printf function ***********/

#define PrintfError( ... )         printf( "Error: "__VA_ARGS__ );  printf( "\n" )
#define PrintfWarn( ... )          printf( "Warn: "__VA_ARGS__ );  printf( "\n" )
#define PrintfInfo( ... )          printf( "Info: " __VA_ARGS__ ); printf( "\n" )
#define PrintfDebug( ... )         printf( "Debug: " __VA_ARGS__ ); printf( "\n" )

#ifdef LOGGING_LEVEL_ERROR
    #define LogError( message )    PrintfError message
#elif defined( LOGGING_LEVEL_WARNING )
    #define LogError( message )    PrintfError message
    #define LogWarn( message )     PrintfWarn message
#elif defined( LOGGING_LEVEL_INFO )
    #define LogError( message )    PrintfError message
    #define LogWarn( message )     PrintfWarn message
    #define LogInfo( message )     PrintfInfo message
#elif defined( LOGGING_LEVEL_DEBUG )
    #define LogError( message )    PrintfError message
    #define LogWarn( message )     PrintfWarn message
    #define LogInfo( message )     PrintfInfo message
    #define LogDebug( message )    PrintfDebug message
#endif /* ifdef LOGGING_LEVEL_ERROR */

/**************************************************/
/* @[code_example_loggingmacros] */

#endif /* ifndef CORE_SNTP_CONFIG_H_ */
