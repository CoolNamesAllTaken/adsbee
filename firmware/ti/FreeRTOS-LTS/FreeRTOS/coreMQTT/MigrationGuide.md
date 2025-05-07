## coreMQTT version >=v2.0.0 Migration Guide

With coreMQTT versions >=v2.0.0, there are some breaking changes that need to be addressed when upgrading.

### Breaking Changes

* The `MQTT_ProcessLoop` function no longer uses a timeout as this led to unavoidable busy-waiting. Thus, the signature of `MQTT_ProcessLoop` changed from `MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext, uint32_t timeoutMs )`  to  `MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext )`. Additionally, `MQTT_ProcessLoop` can now return `MQTTNeedMoreBytes`. A return of `MQTTNeedMoreBytes` means that `MQTT_ProcessLoop` received only a part of an MQTT packet and will need to be called again (probably after a bit of delay) in order to finish receiving the MQTT packet. Thus, to migrate, simply remove the timeout from the `MQTT_ProcessLoop` call and additionally check for if `MQTTNeedMoreBytes` has been returned when checking the status of `MQTT_ProcessLoop`. For example:

**Old Code Snippet**:
```
// Variables used in this example.
MQTTStatus_t status;
uint32_t timeoutMs = 100;
// This context is assumed to be initialized and connected.
MQTTContext_t * pContext;

while( true )
{
     status = MQTT_ProcessLoop( pContext, timeoutMs );

     if( status != MQTTSuccess )
     {
         // Determine the error. It's possible we might need to disconnect
         // the underlying transport connection.
     }
     else
     {
         // Other application functions.
     }
}
```
**New Code Snippet**:
```
// Variables used in this example.
MQTTStatus_t status;
// This context is assumed to be initialized and connected.
MQTTContext_t * pContext;

while( true )
{
     status = MQTT_ProcessLoop( pContext );

     if( status != MQTTSuccess && status != MQTTNeedMoreBytes )
     {
         // Determine the error. It's possible we might need to disconnect
         // the underlying transport connection.
     }
     /* else if only required if the terminating else is empty and the application doesn't want a scenario akin to busy waiting. */
     else if( status == MQTTNeedMoreBytes )
     {
         /* Only a partial MQTT packet is received. Call MQTT_ProcessLoop again; ideally after a small delay. */
     }
     else
     {
         // Other application functions.
     }
}
```

* The `MQTT_ReceiveLoop` function no longer uses a timeout as this led to unavoidable busy-waiting. Thus, the signature of `MQTT_ReceiveLoop` changed from `MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext, uint32_t timeoutMs )`  to  `MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext )`. Additionally, `MQTT_ReceiveLoop` can now return `MQTTNeedMoreBytes`. A return of `MQTTNeedMoreBytes` means that `MQTT_ReceiveLoop` received only a part of an MQTT packet and will need to be called again (probably after a bit of delay) in order to finish receiving the MQTT packet. Thus, to migrate, simply remove the timeout from the `MQTT_ReceiveLoop` call and additionally check for if `MQTTNeedMoreBytes` has been returned when checking the status of `MQTT_ReceiveLoop`. For example:

**Old Code Snippet**:
```
// Variables used in this example.
MQTTStatus_t status;
uint32_t timeoutMs = 100;
// This context is assumed to be initialized and connected.
MQTTContext_t * pContext;

while( true )
{
     status = MQTT_ReceiveLoop( pContext, timeoutMs );

     if( status != MQTTSuccess )
     {
         // Determine the error. It's possible we might need to disconnect
         // the underlying transport connection.
     }
     else
     {
         // Other application functions.
     }
}
```
**New Code Snippet**:
```
// Variables used in this example.
MQTTStatus_t status;
// This context is assumed to be initialized and connected.
MQTTContext_t * pContext;

while( true )
{
     status = MQTT_ReceiveLoop( pContext );

     if( status != MQTTSuccess && status != MQTTNeedMoreBytes )
     {
         // Determine the error. It's possible we might need to disconnect
         // the underlying transport connection.
     }
     /* else if only required if the terminating else is empty and the application doesn't want a scenario akin to busy waiting. */
     else if( status == MQTTNeedMoreBytes )
     {
         /* Only a partial MQTT packet is received. Call MQTT_ReceiveLoop again; ideally after a small delay. */
     }
     else
     {
         // Other application functions.
     }
}
```

* The `TransportInterface_t` structure now has a new member `writev`. It uses scatter-gather approach to send multiple MQTT packet components as a single packet to reduce overhead and improve performance. However, it is COMPLETELY OPTIONAL to implement. To that end, when application(s) initialize a `TransportInterface_t` structure, they **MUST** either set `writev` to a working implementation or set it `NULL`. Not doing this will lead to undefined behavior as the coreMQTT library checks if `writev` is `NULL` to determine if it should be used. For example:

**Old Code Snippet**:
```
TransportInterface_t transport;
// Set transport interface members.
transport.pNetworkInterface = &someNetworkInterface;
transport.send = networkSend;
transport.recv = networkRecv;
```
**New Code Snippet**:
```
TransportInterface_t transport;
// Set transport interface members.
transport.pNetworkInterface = &someNetworkInterface;
transport.send = networkSend;
transport.recv = networkRecv;
transport.writev = NULL;
```

* The `MQTT_Init` function no longer creates buffers to handle QoS > 0 packets, so if planning to use QoS > 0, the `MQTT_InitStatefulQoS` function must also be called on an `MQTTContext_t` after calling `MQTT_Init` on it and before using any other coreMQTT functions with it. If not using QoS > 0, `MQTT_InitStatefulQoS` does not need to be called. For example (code that uses QoS > 0):

**Old Code Snippet**:
```
// Function for obtaining a timestamp.
uint32_t getTimeStampMs();
// Callback function for receiving packets.
void eventCallback(
     MQTTContext_t * pContext,
     MQTTPacketInfo_t * pPacketInfo,
     MQTTDeserializedInfo_t * pDeserializedInfo
);
// Network send.
int32_t networkSend( NetworkContext_t * pContext, const void * pBuffer, size_t bytes );
// Network receive.
int32_t networkRecv( NetworkContext_t * pContext, void * pBuffer, size_t bytes );

MQTTContext_t mqttContext;
TransportInterface_t transport;
MQTTFixedBuffer_t fixedBuffer;
uint8_t buffer[ 1024 ];

// Clear context.
memset( ( void * ) &mqttContext, 0x00, sizeof( MQTTContext_t ) );

// Set transport interface members.
transport.pNetworkInterface = &someNetworkInterface;
transport.send = networkSend;
transport.recv = networkRecv;

// Set buffer members.
fixedBuffer.pBuffer = buffer;
fixedBuffer.size = 1024;

status = MQTT_Init( &mqttContext, &transport, getTimeStampMs, eventCallback, &fixedBuffer );

if( status == MQTTSuccess )
{
     // Do something with mqttContext. The transport and fixedBuffer structs were
     // copied into the context, so the original structs do not need to stay in scope.
}
```
**New Code Snippet**:
```
// Function for obtaining a timestamp.
uint32_t getTimeStampMs();
// Callback function for receiving packets.
void eventCallback(
     MQTTContext_t * pContext,
     MQTTPacketInfo_t * pPacketInfo,
     MQTTDeserializedInfo_t * pDeserializedInfo
);
// Network send.
int32_t networkSend( NetworkContext_t * pContext, const void * pBuffer, size_t bytes );
// Network receive.
int32_t networkRecv( NetworkContext_t * pContext, void * pBuffer, size_t bytes );

MQTTContext_t mqttContext;
TransportInterface_t transport;
MQTTFixedBuffer_t fixedBuffer;
uint8_t buffer[ 1024 ];
static MQTTPubAckInfo_t pOutgoingPublishRecords[ OUTGOING_PUBLISH_RECORD_COUNT ];
static MQTTPubAckInfo_t pIncomingPublishRecords[ INCOMING_PUBLISH_RECORD_COUNT ];

// Clear context.
memset( ( void * ) &mqttContext, 0x00, sizeof( MQTTContext_t ) );

// Set transport interface members.
transport.pNetworkInterface = &someNetworkInterface;
transport.send = networkSend;
transport.recv = networkRecv;
transport.writev = NULL;

// Set buffer members.
fixedBuffer.pBuffer = buffer;
fixedBuffer.size = 1024;

status = MQTT_Init( &mqttContext, &transport, getTimeStampMs, eventCallback, &fixedBuffer );

if( status == MQTTSuccess )
{
    // Initialize MQTT context for QoS > 0. This only has to be done if
    // performing QoS > 0 operations.
    status = MQTT_InitStatefulQoS(pxMQTTContext,
                                   pOutgoingPublishRecords,
                                   OUTGOING_PUBLISH_RECORD_COUNT,
                                   pIncomingPublishRecords,
                                   INCOMING_PUBLISH_RECORD_COUNT);
}

if( status == MQTTSuccess )
{
     // Do something with mqttContext. The transport and fixedBuffer structs were
     // copied into the context, so the original structs do not need to stay in scope.
}
```

* For coreMQTT version >=v2.1.0, the `MQTT_SEND_RETRY_TIMEOUT_MS` macro configuration has been deprecated. It has been replaced with `MQTT_SEND_TIMEOUT_MS`. `MQTT_SEND_RETRY_TIMEOUT_MS` was formerly used to timeout sending an MQTT packet after the transport `send` function failed to transmit any bytes for too long. This timeout would reset each time the transport `send` function sent any bytes, leading to the actual timeout scaling with the number of bytes being sent. In other words, the maximum time for sending a packet was variable. In order to remedy this, the `MQTT_SEND_RETRY_TIMEOUT_MS` macro was replaced with `MQTT_SEND_TIMEOUT_MS`. `MQTT_SEND_TIMEOUT_MS` now sets the maximum duration that coreMQTT will attempt to send an MQTT packet, leading to more consistent timeout behavior across various APIs and packet lengths.

### Additional Changes

* The `MQTT_CancelCallback` function has been added to allow a program to prevent the event callback from being called when receiving an ACK for a sent packet. For example, if a program sends a publish with packet ID 2 and QoS > 0 using `MQTT_Publish`, the program could then call `MQTT_CancelCallback` on packet ID 2 to prevent coreMQTT from calling the event callback when it receives the `PUBACK` for packet ID 2.
