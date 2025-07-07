/*
 * Copyright (c) 2024, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

/*
 * NOTE: When GNU Arm compiler version greater equal than *11.3.Rel1*, there is a linker issue that
 * some system calls are not implemented, such as _close, _fstat and _getpid etc. So add this file
 * including stub functions of system calls to avoid the above linker issue.
 */

#include <stddef.h>
#include <stdint.h>

__attribute__((weak)) void _close(void)
{
}

__attribute__((weak)) void _fstat(void)
{
}

__attribute__((weak)) void _getpid(void)
{
}

__attribute__((weak)) void _isatty(void)
{
}

__attribute__((weak)) void _kill(void)
{
}

__attribute__((weak)) void _lseek(void)
{
}

__attribute__((weak)) void _read(void)
{
}

__attribute__((weak)) void _write(void)
{
}

// In syscalls_stub.c
__attribute__((weak)) void _exit(int status)
{
    while (1)
        ; // Infinite loop for embedded systems
}

__attribute__((weak)) void *_sbrk(int incr)
{
    // Simple heap implementation or return error
    return (void *)-1;
}