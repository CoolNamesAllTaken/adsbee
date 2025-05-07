#include "cbor.h"

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

/* Utils */
size_t nondet_sizet( void );
bool nondet_bool( void );
int nondet_int( void );

/* Returns a non-deterministic CborType */
CborType nondet_CborType( void )
{
    int cborTypes[] =
    {
        CborIntegerType,   CborByteStringType, CborTextStringType,
        CborArrayType,     CborMapType,        CborTagType,       CborSimpleType,
        CborBooleanType,   CborNullType,       CborUndefinedType,
        CborHalfFloatType, CborFloatType,      CborDoubleType,
        CborInvalidType
    };

    int index = nondet_int();

    __CPROVER_assume( index >= 0 && index <= ( sizeof( cborTypes ) / sizeof( cborTypes[ 0 ] ) ) - 1 );

    return cborTypes[ index ];
}

/* Returns a non-deterministic CborError*/
CborError nondet_CborError( void )
{
    int cborErrors[] =
    {
        CborNoError,                      CborUnknownError,                  CborErrorUnknownLength,
        CborErrorIO,                      CborErrorGarbageAtEnd,             CborErrorUnexpectedEOF,
        CborErrorUnexpectedBreak,         CborErrorUnknownType,
        CborErrorIllegalNumber,           CborErrorIllegalSimpleType,
        CborErrorNoMoreStringChunks,      CborErrorUnknownSimpleType,
        CborErrorUnknownTag,              CborErrorInappropriateTagForType,
        CborErrorDuplicateObjectKeys,     CborErrorInvalidUtf8TextString,
        CborErrorExcludedType,            CborErrorExcludedValue,            CborErrorImproperValue,
        CborErrorOverlongEncoding,        CborErrorMapKeyNotString,          CborErrorMapNotSorted,
        CborErrorMapKeysNotUnique,        CborErrorTooManyItems,             CborErrorTooFewItems,
        CborErrorDataTooLarge,            CborErrorNestingTooDeep,           CborErrorUnsupportedType,
        CborErrorUnimplementedValidation, CborErrorJsonObjectKeyIsAggregate,
        CborErrorJsonObjectKeyNotString,  CborErrorJsonNotImplemented,
        CborErrorOutOfMemory,             CborErrorInternalError
    };

    int index = nondet_int();

    __CPROVER_assume( index >= 0 && index <= ( sizeof( cborErrors ) / sizeof( cborErrors[ 0 ] ) ) - 1 );

    return cborErrors[ index ];
}

/* Stubs for functions called by CBOR_Decode_GetStreamResponseMessage() */

CborType cbor_value_get_type( const CborValue * value )
{
    __CPROVER_assert( value != NULL, "CborValue is not NULL." );

    CborType ret = nondet_CborType();

    return ret;
}

CborError cbor_parser_init( const uint8_t * buffer,
                            size_t size,
                            uint32_t flags,
                            CborParser * parser,
                            CborValue * it )
{
    __CPROVER_assert( buffer != NULL, "buffer is not null." );
    __CPROVER_assert( parser != NULL, "parser is not null." );
    __CPROVER_assert( it != NULL, "cbor value is not null." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorUnexpectedEOF ) ||
                      ( ret == CborErrorUnknownType ) ||
                      ( ret == CborErrorIllegalNumber ) ||
                      ( ret == CborErrorUnexpectedBreak ) ||
                      ( ret == CborNoError ) ||
                      ( ret == CborErrorIllegalSimpleType ) );
    return ret;
}

bool cbor_value_is_map( const CborValue * value )
{
    __CPROVER_assert( value != NULL, "CborValue is not NULL." );

    bool ret = nondet_bool();

    return ret;
}

CborError cbor_value_get_int( const CborValue * value,
                              int * result )
{
    __CPROVER_assert( value != NULL, "CborValue is not NULL." );
    __CPROVER_assert( result != NULL, "result is not NULL." );

    /* Only enum value that can be returned by this function */
    return CborNoError;
}

CborError cbor_value_map_find_value( const CborValue * CborMap,
                                     const char * string,
                                     CborValue * element )
{
    __CPROVER_assert( CborMap != NULL, "CborValue is not NULL." );
    __CPROVER_assert( string != NULL, "string is not NULL." );
    __CPROVER_assert( element != NULL, "CborValue is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorDataTooLarge ) ||
                      ( ret == CborNoError ) ||
                      ( ret == CborErrorUnexpectedBreak ) ||
                      ( ret == CborErrorAdvancePastEOF ) ||
                      ( ret == CborErrorNoMoreStringChunks ) ||
                      ( ret == CborErrorIllegalNumber ) );

    return ret;
}

CborError cbor_value_calculate_string_length( const CborValue * value,
                                              size_t * len )
{
    __CPROVER_assert( value != NULL, "CborValue is not NULL" );
    __CPROVER_assert( len != NULL, "length is not NULL" );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorNoMoreStringChunks ) ||
                      ( ret == CborErrorDataTooLarge ) ||
                      ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );
    return ret;
}

CborError cbor_value_copy_byte_string( const CborValue * value,
                                       uint8_t * buffer,
                                       size_t * buflen,
                                       CborValue * next )
{
    __CPROVER_assert( value != NULL, "CborValue is not NULL." );
    __CPROVER_assert( buffer != NULL, "Buffer is not NULL." );
    __CPROVER_assert( buflen != NULL, "bufferLength is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborNoError ) ||
                      ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborErrorNoMoreStringChunks ) ||
                      ( ret == CborErrorDataTooLarge ) ||
                      ( ret == CborErrorUnexpectedEOF ) ||
                      ( ret == CborErrorIllegalType ) ||
                      ( ret == CborErrorIllegalNumber ) );
    return ret;
}

/* Stubs for CBOR_Encode_GetStreamRequestMessage */

void cbor_encoder_init( CborEncoder * encoder,
                        uint8_t * buffer,
                        size_t size,
                        int flags )
{
    __CPROVER_assert( encoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( buffer != NULL, "Buffer is not NULL." );
}

CborError cbor_encoder_create_map( CborEncoder * parentEncoder,
                                   CborEncoder * mapEncoder,
                                   size_t length )
{
    __CPROVER_assert( parentEncoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( mapEncoder != NULL, "CborEncoder is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorDataTooLarge ) ||
                      ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );

    return ret;
}

CborError cbor_encode_text_stringz( CborEncoder * encoder,
                                    const char * string )
{
    __CPROVER_assert( encoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( string != NULL, "String is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );
    return ret;
}

CborError cbor_encode_int( CborEncoder * encoder,
                           int64_t value )
{
    __CPROVER_assert( encoder != NULL, "CborEncoder is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );
    return ret;
}

CborError cbor_encode_byte_string( CborEncoder * encoder,
                                   const uint8_t * string,
                                   size_t length )
{
    __CPROVER_assert( encoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( string != NULL, "String is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );
    return ret;
}

CborError cbor_encoder_close_container_checked( CborEncoder * parentEncoder,
                                                const CborEncoder * containerEncoder )
{
    __CPROVER_assert( parentEncoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( containerEncoder != NULL, "CborEncoder is not NULL." );

    CborError ret = nondet_CborError();

    __CPROVER_assume( ( ret == CborErrorTooManyItems ) ||
                      ( ret == CborErrorTooFewItems ) ||
                      ( ret == CborErrorOutOfMemory ) ||
                      ( ret == CborNoError ) );
    return ret;
}

size_t cbor_encoder_get_buffer_size( const CborEncoder * encoder,
                                     const uint8_t * buffer )
{
    __CPROVER_assert( encoder != NULL, "CborEncoder is not NULL." );
    __CPROVER_assert( buffer != NULL, "Buffer is not NULL." );

    return nondet_sizet();
}
