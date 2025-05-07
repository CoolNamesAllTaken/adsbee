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

#ifndef DUMP_PACKETS_H


#define DUMP_PACKETS_H

#ifndef dumpMAX_DUMP_ENTRIES
    #define dumpMAX_DUMP_ENTRIES    16
#endif

#define flag_ICMP4                  0x00000001UL
#define flag_ICMP6                  0x00000002UL
#define flag_UDP                    0x00000004UL
#define flag_TCP                    0x00000008UL
#define flag_DNS                    0x00000010UL
#define flag_REPLY                  0x00000020UL
#define flag_REQUEST                0x00000040UL
#define flag_SYN                    0x00000080UL
#define flag_FIN                    0x00000100UL
#define flag_RST                    0x00000200UL
#define flag_ACK                    0x00000400UL
#define flag_IN                     0x00000800UL
#define flag_OUT                    0x00001000UL
#define flag_FRAME_ARP              0x00002000UL
#define flag_ARP                    0x00004000UL
#define flag_UNKNOWN                0x00008000UL
#define flag_FRAME_4                0x00010000UL
#define flag_FRAME_6                0x00020000UL
#define flag_Unknown_FRAME          0x00040000UL

/** @brief Structure to hold information about one dump entry.
 */
typedef struct xDumpEntry
{
    uint32_t ulMask; /**< The mask of the entry */
    size_t uxMax;    /**< The max value of the entry */
    size_t uxCount;  /**< The count of the entry */
} DumpEntry_t;

/** @brief Structure to hold information of all the entries in this data dump. */
typedef struct xDumpEntries
{
    size_t uxEntryCount;                          /**< The number of entries*/
    DumpEntry_t xEntries[ dumpMAX_DUMP_ENTRIES ]; /**< Array of struct for all the entries */
} DumpEntries_t;

#if ( ipconfigUSE_DUMP_PACKETS != 0 )

    extern void dump_packet_init( const char * pcFileName,
                                  DumpEntries_t * pxEntries );
    #define iptraceDUMP_INIT( pcFileName, pxEntries ) \
    dump_packet_init( pcFileName, pxEntries )

    extern void dump_packet( const uint8_t * pucBuffer,
                             size_t uxLength,
                             BaseType_t xIncoming );
    #define iptraceDUMP_PACKET( pucBuffer, uxLength, xIncoming ) \
    dump_packet( pucBuffer, uxLength, xIncoming )

#endif /* if ( ipconfigUSE_DUMP_PACKETS != 0 ) */

#endif /* ifndef DUMP_PACKETS_H */
