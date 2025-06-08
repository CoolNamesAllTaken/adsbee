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

#include "FreeRTOS.h"
#include "portmacro.h"
#include "list.h"

#undef listSET_LIST_ITEM_OWNER
void listSET_LIST_ITEM_OWNER( ListItem_t * pxListItem,
                              void * owner );

#undef listGET_HEAD_ENTRY
ListItem_t * listGET_HEAD_ENTRY( List_t * pxList );

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

#undef listLIST_IS_INITIALISED
BaseType_t listLIST_IS_INITIALISED( List_t * pxList );

/*
 * Returns pdTRUE if the IP task has been created and is initialised.  Otherwise
 * returns pdFALSE.
 */
BaseType_t xIPIsNetworkTaskReady( void );

/*
 * The same as above, but a struct as a parameter, containing:
 *      eIPEvent_t eEventType;
 *      void *pvData;
 */
BaseType_t xSendEventStructToIPTask( const IPStackEvent_t * pxEvent,
                                     TickType_t uxTimeout );

/* Returns pdTRUE is this function is called from the IP-task */
BaseType_t xIsCallingFromIPTask( void );

/* Get the size of the IP-header.
 * 'usFrameType' must be filled in if IPv6is to be recognised. */
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Returns a pointer to the original NetworkBuffer from a pointer to a UDP
 * payload buffer.
 */
NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer );


/*
 * Send the event eEvent to the IP task event queue, using a block time of
 * zero.  Return pdPASS if the message was sent successfully, otherwise return
 * pdFALSE.
 */
BaseType_t xSendEventToIPTask( eIPEvent_t eEvent );

/*
 * Internal: Sets a new state for a TCP socket and performs the necessary
 * actions like calling a OnConnected handler to notify the socket owner.
 */
#if ( ipconfigUSE_TCP == 1 )
    void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                          enum eTCP_STATE eTCPState );
#endif /* ipconfigUSE_TCP */

/* Check a single socket for retransmissions and timeouts */
BaseType_t xTCPSocketCheck( FreeRTOS_Socket_t * pxSocket );

/* Get the size of the IP-header.
 * The socket is checked for its type: IPv4 or IPv6. */
size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket );

#endif /* ifndef LIST_MACRO_H */
