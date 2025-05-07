#ifndef PKCS11_TEST_WRAP
#define PKCS11_TEST_WRAP

/* This file contains definitions for use when preprocessing the pkcs11.h header
 *  file prior to generating a compatible mock */
#define CK_PTR      *
#define NULL_PTR    0
#define CK_DEFINE_FUNCTION( returnType, name )             returnType name
#define CK_DECLARE_FUNCTION( returnType, name )            returnType name
#define CK_DECLARE_FUNCTION_POINTER( returnType, name )    returnType( CK_PTR name )
#define CK_CALLBACK_FUNCTION( returnType, name )           returnType( CK_PTR name )

/* #include PKCS11_HDR_PATH */

#endif /* PKCS11_TEST_WRAP */
