# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# corePKCS11 library source files.
set( PKCS_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/core_pkcs11.c"
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/mbedtls/core_pkcs11_mbedtls.c"
     "${CMAKE_CURRENT_LIST_DIR}/source/core_pki_utils.c"
     )

# corePKCS11 library public include directories.
set( PKCS_INCLUDE_PUBLIC_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/pkcs11/published/2-40-errata-1"
     "${CMAKE_CURRENT_LIST_DIR}/source/include"
     )

# corePKCS11 PAL Posix source files.
set( PKCS_PAL_POSIX_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/core_pkcs11_pal_utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/posix/core_pkcs11_pal.c"
     )

# corePKCS11 PAL Windows source files.
set( PKCS_PAL_WINDOWS_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/core_pkcs11_pal_utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/freertos_winsim/core_pkcs11_pal.c"
     )

# corePKCS11 PAL shared include directories.
set( PKCS_PAL_INCLUDE_PUBLIC_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/source/portable/os"
     )
