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

#ifndef LIST_MACRO_H
#define LIST_MACRO_H

#include <FreeRTOS.h>
#include <portmacro.h>
#include <list.h>

#include "FreeRTOS_IPv6_Private.h"

extern NetworkInterface_t xInterfaces[ 1 ];

#undef listSET_LIST_ITEM_OWNER
void listSET_LIST_ITEM_OWNER( ListItem_t * pxListItem,
                              void * owner );

#undef listGET_END_MARKER
ListItem_t * listGET_END_MARKER( List_t * pxList );

#undef listGET_NEXT
ListItem_t * listGET_NEXT( const ListItem_t * pxListItem );

#undef  listLIST_IS_EMPTY
BaseType_t listLIST_IS_EMPTY( const List_t * pxList );

#undef  listGET_OWNER_OF_HEAD_ENTRY
void * listGET_OWNER_OF_HEAD_ENTRY( const List_t * pxList );

#undef listIS_CONTAINED_WITHIN
BaseType_t listIS_CONTAINED_WITHIN( List_t * list,
                                    const ListItem_t * listItem );

#undef listGET_LIST_ITEM_VALUE
TickType_t listGET_LIST_ITEM_VALUE( const ListItem_t * listItem );

#undef listSET_LIST_ITEM_VALUE
void listSET_LIST_ITEM_VALUE( ListItem_t * listItem,
                              TickType_t itemValue );


#undef listLIST_ITEM_CONTAINER
List_t * listLIST_ITEM_CONTAINER( const ListItem_t * listItem );

#undef listCURRENT_LIST_LENGTH
UBaseType_t listCURRENT_LIST_LENGTH( List_t * list );

#undef listGET_ITEM_VALUE_OF_HEAD_ENTRY
TickType_t listGET_ITEM_VALUE_OF_HEAD_ENTRY( List_t * list );

#undef listGET_LIST_ITEM_OWNER
void * listGET_LIST_ITEM_OWNER( const ListItem_t * listItem );

/**
 * @brief Reduce the age counter in each entry within the ND cache.  An entry is no
 * longer considered valid and is deleted if its age reaches zero.
 * Just before getting to zero, 3 times a neighbour solicitation will be sent.
 */
void vNDAgeCache( void );

/**
 * >>>>>>> afcedead21c747cef64f07c7fedd50df75bcbd10
 * @brief Work on the RA/SLAAC processing.
 * @param[in] xDoReset: WHen true, the state-machine will be reset and initialised.
 * @param[in] pxEndPoint: The end-point for which the RA/SLAAC process should be done..
 */
void vRAProcess( BaseType_t xDoReset,
                 NetworkEndPoint_t * pxEndPoint );

/* This function shall be defined by the application. */
void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                           struct xNetworkEndPoint * pxEndPoint );


/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialise the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
struct xNetworkInterface * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      struct xNetworkInterface * pxInterface );


/* The function 'prvAllowIPPacket()' checks if a IPv6 packets should be processed. */
eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
                                               const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                               UBaseType_t uxHeaderLength );


/* Return IPv6 header extension order number */
BaseType_t xGetExtensionOrder( uint8_t ucProtocol,
                               uint8_t ucNextHeader );



/** @brief Handle the IPv6 extension headers. */
eFrameProcessingResult_t eHandleIPv6ExtensionHeaders( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                      BaseType_t xDoRemove );

/*
 * If ulIPAddress is already in the ND cache table then reset the age of the
 * entry back to its maximum value.  If ulIPAddress is not already in the ND
 * cache table then add it - replacing the oldest current entry if there is not
 * a free space available.
 */
void vNDRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                           const IPv6_Address_t * pxIPAddress,
                           NetworkEndPoint_t * pxEndPoint );

/* prvProcessICMPMessage_IPv6() is declared in FreeRTOS_routing.c
 * It handles all ICMP messages except the PING requests. */
eFrameProcessingResult_t prvProcessICMPMessage_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/* Return pdTRUE if all end-points are up.
 * When pxInterface is null, all end-points will be checked. */
BaseType_t FreeRTOS_AllEndPointsUp( const struct xNetworkInterface * pxInterface );

#endif /* ifndef LIST_MACRO_H */
