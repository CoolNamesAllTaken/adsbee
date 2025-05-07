int32_t publicTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                              UBaseType_t uxOptionsLength )
{
    prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );
}

BaseType_t publicTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t ** ppxNetworkBuffer )
{
    prvTCPHandleState( pxSocket, ppxNetworkBuffer );
}
