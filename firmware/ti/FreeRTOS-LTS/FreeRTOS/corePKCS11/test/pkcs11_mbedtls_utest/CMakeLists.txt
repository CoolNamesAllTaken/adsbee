project("core_pkcs11_mbedtls_utest")

include(${MODULE_ROOT_DIR}/pkcsFilePaths.cmake)
include(${MODULE_ROOT_DIR}/tools/unity.cmake)
include(${MODULE_ROOT_DIR}/tools/cmock.cmake)
include(${MODULE_ROOT_DIR}/tools/pkcs11_api.cmake)

add_test_target(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_utest.c)

target_add_test_runner(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml core_pkcs11_mbedtls_utest.c
)

target_include_directories(core_pkcs11_mbedtls_utest PUBLIC "${MODULE_ROOT_DIR}/test/include")

target_link_libraries(core_pkcs11_mbedtls_utest PRIVATE MbedTLS2::interface)

set(MBEDTLS_INC "${mbedtls_2_SOURCE_DIR}/include/mbedtls")
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml
    "${CMAKE_CURRENT_LIST_DIR}/../include/mock_osal.h"
)
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml
    "${CMAKE_CURRENT_LIST_DIR}/../include/malloc_stub.h"
)
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml
    "${MODULE_ROOT_DIR}/source/include/core_pkcs11_pal.h"
)
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml
    "${MODULE_ROOT_DIR}/source/include/core_pki_utils.h"
)
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/ctr_drbg.h"
)
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/sha256.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/base64.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/bignum.h")
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/entropy.h"
)
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/md.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/rsa.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/ecp.h")
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/pk_internal.h"
)
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/ecdsa.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/pk.h")
target_add_mock(
    core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/x509_crt.h"
)
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/cmac.h")
target_add_mock(core_pkcs11_mbedtls_utest core_pkcs11_mbedtls_config.yml "${MBEDTLS_INC}/cipher.h")

target_compile_options(core_pkcs11_mbedtls_utest PRIVATE -Wno-attributes)

target_include_directories(
    core_pkcs11_mbedtls_utest
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/include"
    PRIVATE "${CMAKE_CURRENT_BINARY_DIR}"
    PRIVATE "${MODULE_ROOT_DIR}/source/include"
    PRIVATE "../include"
)

target_link_libraries(core_pkcs11_mbedtls_utest PRIVATE cmock)

add_library(core_pkcs11_mbedtls STATIC)
target_sources(
    core_pkcs11_mbedtls PRIVATE ${MODULE_ROOT_DIR}/source/portable/mbedtls/core_pkcs11_mbedtls.c
)
target_link_libraries(core_pkcs11_mbedtls PRIVATE MbedTLS2::interface pkcs11_api)

target_include_directories(
    core_pkcs11_mbedtls
    PUBLIC "${CMAKE_CURRENT_LIST_DIR}/../include"
    PUBLIC "${MODULE_ROOT_DIR}/source/include"
)

target_compile_options(
    core_pkcs11_mbedtls PRIVATE "-include${MODULE_ROOT_DIR}/test/include/pkcs11_defs.h"
    PRIVATE "-include${PKCS11_API_PATH}/pkcs11.h"
)

target_compile_options(
    core_pkcs11_mbedtls_utest PRIVATE "-include${MODULE_ROOT_DIR}/test/include/pkcs11_defs.h"
    PRIVATE "-include${PKCS11_API_PATH}/pkcs11.h"
)

target_enable_gcov(core_pkcs11_mbedtls PRIVATE)
target_link_libraries(core_pkcs11_mbedtls_utest PRIVATE core_pkcs11_mbedtls)
