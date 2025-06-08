/*
 * backoffAlgorithm v1.4.1
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

/*
 * How to catch an assert:
 * - save a jump buffer where execution will resume after the assert
 * - setup a handler for the abort signal, call longjmp within
 * - optional - close stderr ( fd 2 ) to discard the assert message
 *
 * Unity also does a longjmp within its TEST_ASSERT* macros,
 * so the macro below restores stderr and the prior abort handler
 * before calling the Unity macro.
 */

#ifndef CATCH_ASSERT_H_
#define CATCH_ASSERT_H_

#include <setjmp.h>
#include <signal.h>
#include <unistd.h>

#ifndef CATCH_JMPBUF
    #define CATCH_JMPBUF    waypoint_
#endif

static jmp_buf CATCH_JMPBUF;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-function"
static void catchHandler_( int signal )
{
    longjmp( CATCH_JMPBUF, signal );
}
#pragma GCC diagnostic pop

#define catch_assert( x )                    \
    do {                                     \
        int try = 0, catch = 0;              \
        int saveFd = dup( 2 );               \
        struct sigaction sa = { 0 }, saveSa; \
        sa.sa_handler = catchHandler_;       \
        sigaction( SIGABRT, &sa, &saveSa );  \
        close( 2 );                          \
        if( setjmp( CATCH_JMPBUF ) == 0 )    \
        {                                    \
            try++;                           \
            x;                               \
        }                                    \
        else                                 \
        {                                    \
            catch++;                         \
        }                                    \
        sigaction( SIGABRT, &saveSa, NULL ); \
        dup2( saveFd, 2 );                   \
        close( saveFd );                     \
        TEST_ASSERT_EQUAL( try, catch );     \
    } while( 0 )

#endif /* ifndef CATCH_ASSERT_H_ */
