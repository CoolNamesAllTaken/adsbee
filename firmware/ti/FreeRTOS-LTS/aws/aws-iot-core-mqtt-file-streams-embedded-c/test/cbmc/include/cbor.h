/**
 * Minimum header file for tinyCBOR for use with cbmc proofs.
 */

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

typedef enum CborError
{
    CborNoError = 0,

    /* errors in all modes */
    CborUnknownError,
    CborErrorUnknownLength, /* request for length in array, map, or string with indeterminate length */
    CborErrorAdvancePastEOF,
    CborErrorIO,

    /* parser errors streaming errors */
    CborErrorGarbageAtEnd = 256,
    CborErrorUnexpectedEOF,
    CborErrorUnexpectedBreak,
    CborErrorUnknownType,       /* can only happen in major type 7 */
    CborErrorIllegalType,       /* type not allowed here */
    CborErrorIllegalNumber,
    CborErrorIllegalSimpleType, /* types of value less than 32 encoded in two bytes */
    CborErrorNoMoreStringChunks,

    /* parser errors in strict mode parsing only */
    CborErrorUnknownSimpleType = 512,
    CborErrorUnknownTag,
    CborErrorInappropriateTagForType,
    CborErrorDuplicateObjectKeys,
    CborErrorInvalidUtf8TextString,
    CborErrorExcludedType,
    CborErrorExcludedValue,
    CborErrorImproperValue,
    CborErrorOverlongEncoding,
    CborErrorMapKeyNotString,
    CborErrorMapNotSorted,
    CborErrorMapKeysNotUnique,

    /* encoder errors */
    CborErrorTooManyItems = 768,
    CborErrorTooFewItems,

    /* internal implementation errors */
    CborErrorDataTooLarge = 1024,
    CborErrorNestingTooDeep,
    CborErrorUnsupportedType,
    CborErrorUnimplementedValidation,

    /* errors in converting to JSON */
    CborErrorJsonObjectKeyIsAggregate = 1280,
    CborErrorJsonObjectKeyNotString,
    CborErrorJsonNotImplemented,

    CborErrorOutOfMemory = ( int )( ~0U / 2 + 1 ),
    CborErrorInternalError = ( int )( ~0U / 2 ) /* INT_MAX on two's complement machines */
} CborError;

typedef enum CborType
{
    CborIntegerType = 0x00,
    CborByteStringType = 0x40,
    CborTextStringType = 0x60,
    CborArrayType = 0x80,
    CborMapType = 0xa0,
    CborTagType = 0xc0,
    CborSimpleType = 0xe0,
    CborBooleanType = 0xf5,
    CborNullType = 0xf6,
    CborUndefinedType = 0xf7,
    CborHalfFloatType = 0xf9,
    CborFloatType = 0xfa,
    CborDoubleType = 0xfb,

    CborInvalidType = 0xff /* equivalent to the break byte, so it will never be used */
} CborType;

struct CborParserOperations
{
    bool (* can_read_bytes)( void * token,
                             size_t len );
    void *(* read_bytes)( void * token,
                          void * dst,
                          size_t offset,
                          size_t len );
    void (* advance_bytes)( void * token,
                            size_t len );
    CborError (* transfer_string)( void * token,
                                   const void ** userptr,
                                   size_t offset,
                                   size_t len );
};

enum CborParserGlobalFlags
{
    CborParserFlag_ExternalSource = 0x01
};

struct CborParser
{
    union
    {
        const uint8_t * end;
        const struct CborParserOperations * ops;
    }
    source;
    enum CborParserGlobalFlags flags;
};
typedef struct CborParser CborParser;

typedef enum CborEncoderAppendType
{
    CborEncoderAppendCborData = 0,
    CborEncoderAppendStringData = 1
} CborEncoderAppendType;

typedef CborError (* CborEncoderWriteFunction)( void *,
                                                const void *,
                                                size_t,
                                                CborEncoderAppendType );

struct CborEncoder
{
    union
    {
        uint8_t * ptr;
        ptrdiff_t bytes_needed;
        CborEncoderWriteFunction writer;
    }
    data;
    uint8_t * end;
    size_t remaining;
    int flags;
};
typedef struct CborEncoder CborEncoder;

struct CborValue
{
    const CborParser * parser;
    union
    {
        const uint8_t * ptr;
        void * token;
    }
    source;
    uint32_t remaining;
    uint16_t extra;
    uint8_t type;
    uint8_t flags;
};
typedef struct CborValue CborValue;



CborType cbor_value_get_type( const CborValue * value );

CborError cbor_parser_init( const uint8_t * buffer,
                            size_t size,
                            uint32_t flags,
                            CborParser * parser,
                            CborValue * it );

bool cbor_value_is_map( const CborValue * value );

CborError cbor_value_map_find_value( const CborValue * CborMap,
                                     const char * string,
                                     CborValue * element );

CborError cbor_value_calculate_string_length( const CborValue * value,
                                              size_t * len );

uint64_t _cbor_value_decode_int64_internal( const CborValue * value );

CborError cbor_value_copy_byte_string( const CborValue * value,
                                       uint8_t * buffer,
                                       size_t * buflen,
                                       CborValue * next );

void cbor_encoder_init( CborEncoder * encoder,
                        uint8_t * buffer,
                        size_t size,
                        int flags );

CborError cbor_encoder_create_map( CborEncoder * parentEncoder,
                                   CborEncoder * mapEncoder,
                                   size_t length );

CborError cbor_encode_text_stringz( CborEncoder * encoder,
                                    const char * string );

CborError cbor_encode_int( CborEncoder * encoder,
                           int64_t value );

CborError cbor_encode_byte_string( CborEncoder * encoder,
                                   const uint8_t * string,
                                   size_t length );

CborError cbor_encoder_close_container_checked( CborEncoder * parentEncoder,
                                                const CborEncoder * containerEncoder );

size_t cbor_encoder_get_buffer_size( const CborEncoder * encoder,
                                     const uint8_t * buffer );
