project("pkcs11_utils_utest")

include(${MODULE_ROOT_DIR}/pkcsFilePaths.cmake)
include(${MODULE_ROOT_DIR}/tools/unity.cmake)
include(${MODULE_ROOT_DIR}/tools/cmock.cmake)
include(${MODULE_ROOT_DIR}/tools/mbedtls.cmake)
include(${MODULE_ROOT_DIR}/tools/pkcs11_api.cmake)

add_test_target(pkcs11_utils_utest pkcs11_utils_utest.c)

target_add_test_runner(pkcs11_utils_utest pkcs11_utils_config.yml pkcs11_utils_utest.c)

target_link_libraries(pkcs11_utils_utest PRIVATE MbedTLS2::interface)

target_add_mock(
    pkcs11_utils_utest pkcs11_utils_config.yml "${mbedtls_2_SOURCE_DIR}/include/mbedtls/error.h"
)
target_link_libraries(pkcs11_utils_utest PRIVATE cmock)

target_include_directories(
    pkcs11_utils_utest
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/include"
    PRIVATE "${CMAKE_CURRENT_BINARY_DIR}"
    PRIVATE "${MODULE_ROOT_DIR}/source/include"
    PRIVATE "../include"
)

add_library(pkcs11_utils STATIC)
target_sources(
    pkcs11_utils
    PRIVATE "${MODULE_ROOT_DIR}/source/core_pki_utils.c"
    PRIVATE "../include/logging_stack.h"
    PRIVATE "../include/logging_levels.h"
)

target_link_libraries(pkcs11_utils PRIVATE MbedTLS2::mbedcrypto)

target_include_directories(
    pkcs11_utils PRIVATE "../include" PUBLIC "${MODULE_ROOT_DIR}/source/include"
)

target_enable_gcov(pkcs11_utils PRIVATE)
target_link_libraries(pkcs11_utils_utest PRIVATE pkcs11_utils)
