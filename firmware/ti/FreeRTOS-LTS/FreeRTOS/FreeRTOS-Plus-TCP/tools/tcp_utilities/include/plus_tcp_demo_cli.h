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

#ifndef PLUS_TCP_DEMO_CLI_H

    #if __cplusplus
    extern "C" {
    #endif

/*
 * Handle a CLI command.
 * Returns zero when the command was recognised and handled.
 */
    BaseType_t xHandleTestingCommand( char * pcBuffer,
                                      size_t uxBufferSize );

/*
 * Do the regular checks.
 */
    void xHandleTesting( void );

/*
 * Show all properties of an end-point.
 */
    void showEndPoint( NetworkEndPoint_t * pxEndPoint );

/*/ * 'xServerSemaphore' should be declared in main.c * / */
/*extern SemaphoreHandle_t xServerSemaphore; */

    #if __cplusplus
}         /* extern "C" */
    #endif

    extern int verboseLevel;

#endif /* PLUS_TCP_DEMO_CLI_H */
