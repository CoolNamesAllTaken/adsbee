#include <stdbool.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include "MQTTFileDownloader_base64.h"
#include "MQTTFileDownloader_cbor.h"
#include "MQTTFileDownloader.h"
#include "core_json.h"


#ifndef UNWIND_COUNT
    #define UNWIND_COUNT    10
#endif

#ifndef __CPROVER__
    bool __CPROVER_assume( bool );
    bool __CPROVER_r_ok( const void *,
                         ... );
    bool __CPROVER_rw_ok( const void *,
                          ... );
#endif

/* Utils */
size_t nondet_sizet( void );
int nondet_int( void );

#define CBMC_MAX_OBJECT_SIZE       ( PTRDIFF_MAX )
#define CBMC_MAX_BUFSIZE           ( UNWIND_COUNT - 1 )
#define CBMC_STREAMNAME_MAX_LEN    ( UNWIND_COUNT - 1 )
#define CBMC_THINGNAME_MAX_LEN     ( UNWIND_COUNT - 1 )
#define CBMC_TOPIC_MAX_LEN         ( UNWIND_COUNT - 1 )
#define CBMC_MESSAGE_MAX_LEN       ( UNWIND_COUNT - 1 )

static bool validateStr( char * str )
{
    return( str != NULL );
}

static char * nondetStr( void )
{
    char * ret;

    ret = malloc( nondet_sizet() );
    __CPROVER_assume( validateStr( ret ) );
    return ret;
}

DataType_t nondet_DataType_T( void )
{
    int Types[] = { DATA_TYPE_CBOR, DATA_TYPE_JSON };

    int index = nondet_int();

    __CPROVER_assume( index >= 0 && index <= ( sizeof( Types ) / sizeof( Types[ 0 ] ) ) - 1 );

    return Types[ index ];
}

void proof_mqttDownloader_init( void )
{
    MqttFileDownloaderContext_t context = { 0 };
    char * streamName;
    size_t streamNameLength;
    char * thingName;
    size_t thingNameLength;
    DataType_t dataType = nondet_DataType_T();
    uint8_t ret;

    __CPROVER_assume( streamNameLength <= CBMC_STREAMNAME_MAX_LEN );
    streamName = malloc( streamNameLength );

    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    ret = mqttDownloader_init( &context,
                               streamName,
                               streamNameLength,
                               thingName,
                               thingNameLength,
                               dataType );

    __CPROVER_assert( ret >= MQTTFileDownloaderSuccess && ret <= MQTTFileDownloaderDataDecodingFailed,
                      "Return value is in range of MQTTFileDownloaderStatus_t" );
}

void proof_mqttDownloader_createGetDataBlockRequest( void )
{
    DataType_t dataType = nondet_DataType_T();
    uint16_t fileId;
    uint32_t blockSize;
    uint16_t blockOffset;
    uint32_t numberOfBlocksRequested;
    char * getStreamRequest;
    size_t getStreamRequestLength;
    size_t ret;

    getStreamRequest = malloc( getStreamRequestLength );

    ret = mqttDownloader_createGetDataBlockRequest( dataType,
                                                    fileId,
                                                    blockSize,
                                                    blockOffset,
                                                    numberOfBlocksRequested,
                                                    getStreamRequest,
                                                    getStreamRequestLength );
}

void proof_mqttDownloader_isDataBlockReceived( void )
{
    MqttFileDownloaderContext_t context = { 0 };
    char * topic;
    size_t topicLength;
    bool ret;

    __CPROVER_assume( topicLength <= CBMC_TOPIC_MAX_LEN );
    topic = malloc( topicLength );

    ret = mqttDownloader_isDataBlockReceived( &context,
                                              topic,
                                              topicLength );
}

void proof_mqttDownloader_processReceivedDataBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };
    uint8_t * message;
    size_t messageLength;
    int32_t fileId;
    int32_t blockId;
    int32_t blockSize;
    uint8_t * data;
    size_t dataLength;
    bool ret;

    __CPROVER_assume( ( &context )->dataType == DATA_TYPE_JSON ||
                      ( &context )->dataType == DATA_TYPE_CBOR );

    __CPROVER_assume( messageLength <= CBMC_TOPIC_MAX_LEN );
    message = malloc( messageLength );

    __CPROVER_assume( dataLength >= 256 );
    data = malloc( dataLength );

    ret = mqttDownloader_processReceivedDataBlock( &context,
                                                   message,
                                                   messageLength,
                                                   &fileId,
                                                   &blockId,
                                                   &blockSize,
                                                   data,
                                                   &dataLength );
}

void proof_mqttDownloader_base64_Decode( void )
{
    uint8_t * dest;
    const size_t destLen;
    size_t resultLen;
    const uint8_t * encodedData;
    const size_t encodedLen;
    Base64Status_t ret;

    __CPROVER_assume( destLen <= CBMC_MAX_BUFSIZE );
    dest = malloc( destLen );

    __CPROVER_assume( &resultLen != NULL );

    __CPROVER_assume( encodedLen <= CBMC_MAX_BUFSIZE );
    encodedData = malloc( encodedLen );

    ret = base64_Decode( dest,
                         destLen,
                         &resultLen,
                         encodedData,
                         encodedLen );

    __CPROVER_assert( ret >= Base64Success && ret <= Base64InvalidPaddingSymbol,
                      "Return value is in range of Base64Status_t." );
}

void proof_CBOR_Encode_GetStreamRequestMessage( void )
{
    uint8_t * messageBuffer;
    size_t messageBufferSize;
    size_t encodedMessageSize;
    const char clientToken = nondetStr();
    uint32_t fileId;
    uint32_t blockSize;
    uint32_t blockOffset;
    const uint8_t blockBitmap = nondetStr();
    size_t blockBitmapSize = sizeof( blockBitmap );
    uint32_t numOfBlocksRequested;
    bool ret;

    __CPROVER_assume( messageBufferSize <= UINT32_MAX );
    messageBuffer = malloc( messageBufferSize );

    __CPROVER_assume( numOfBlocksRequested <= UNWIND_COUNT );

    ret = CBOR_Encode_GetStreamRequestMessage( messageBuffer,
                                               messageBufferSize,
                                               &encodedMessageSize,
                                               &clientToken,
                                               fileId,
                                               blockSize,
                                               blockOffset,
                                               &blockBitmap,
                                               blockBitmapSize,
                                               numOfBlocksRequested );
}

void proof_CBOR_Decode_GetStreamResponseMessage( void )
{
    const uint8_t * messageBuffer;
    size_t messageSize;
    int32_t fileId;
    int32_t blockId;
    int32_t blockSize;
    uint8_t * payload;
    size_t payloadSize;
    bool ret;

    __CPROVER_assume( messageSize <= UNWIND_COUNT );
    messageBuffer = malloc( messageSize );

    __CPROVER_assume( payloadSize <= UNWIND_COUNT );
    payload = malloc( payloadSize );

    ret = CBOR_Decode_GetStreamResponseMessage( messageBuffer,
                                                messageSize,
                                                &fileId,
                                                &blockId,
                                                &blockSize,
                                                &payload,
                                                &payloadSize );
}

int main()
{
    /* Functions in MQTTFileDownloader.c */
    proof_mqttDownloader_init();
    proof_mqttDownloader_createGetDataBlockRequest();
    proof_mqttDownloader_isDataBlockReceived();
    proof_mqttDownloader_processReceivedDataBlock();
    /* Functions in MQTTDownloader_base64.c */
    proof_mqttDownloader_base64_Decode();
    /* Functions in MQTTDownloader_cbor.c */
    proof_CBOR_Encode_GetStreamRequestMessage();
    proof_CBOR_Decode_GetStreamResponseMessage();
}
