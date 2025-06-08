project("pkcs11 mbedtls integration test")

include(${MODULE_ROOT_DIR}/pkcsFilePaths.cmake)
include(${MODULE_ROOT_DIR}/tools/unity.cmake)
include(${MODULE_ROOT_DIR}/tools/cmock.cmake)
include(${MODULE_ROOT_DIR}/tools/pkcs11_api.cmake)

add_library(target_lib INTERFACE)
target_sources(target_lib INTERFACE "${PKCS_SOURCES}")

target_include_directories(
    target_lib
    INTERFACE "${PKCS_INCLUDE_PUBLIC_DIRS}"
    INTERFACE "${PKCS_PAL_INCLUDE_PUBLIC_DIRS}"
    INTERFACE "${CMAKE_CURRENT_LIST_DIR}"
    INTERFACE "${CMAKE_CURRENT_LIST_DIR}/../include"
)
target_link_libraries(target_lib INTERFACE pkcs11_api)

add_library(target_lib_mb2 STATIC)
target_link_libraries(target_lib_mb2 PRIVATE target_lib MbedTLS2::mbedcrypto)

add_library(target_lib_mb3 STATIC)
target_link_libraries(target_lib_mb3 PRIVATE target_lib MbedTLS3::mbedcrypto)

add_library(mbedtls_test INTERFACE)
target_sources(mbedtls_test INTERFACE mbedtls_integration_test.c INTERFACE "${PKCS_PAL_POSIX_SOURCES}")

target_add_test_runner(mbedtls_test core_pkcs11_mbedtls_config.yml mbedtls_integration_test.c)
target_link_libraries(
    mbedtls_test
    INTERFACE target_lib
    INTERFACE unity
    INTERFACE pkcs11_api
)

target_include_directories(
    mbedtls_test
    INTERFACE "${MODULE_ROOT_DIR}/source/include"
    INTERFACE "${MODULE_ROOT_DIR}/source/portable/os"
    INTERFACE "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils"
    INTERFACE "${CMAKE_CURRENT_LIST_DIR}"
)

set_source_files_properties(
    "${MODULE_ROOT_DIR}/source/portable/mbedtls/core_pkcs11_mbedtls.c"
    PROPERTIES COMPILE_FLAGS "-Wno-pedantic -Wno-error"
)

set_source_files_properties(
    "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils/mbedtls_utils.c"
    PROPERTIES COMPILE_FLAGS "-Wno-pedantic -Wno-error"
)

# ====================================  Mbedtls 2.x binary ========================================
add_executable(integration_mbedtls_2)

target_link_libraries(integration_mbedtls_2 PRIVATE mbedtls_test target_lib_mb2)

target_link_libraries(integration_mbedtls_2 PRIVATE MbedTLS2::mbedtls)

set_target_properties(
    integration_mbedtls_2 PROPERTIES COMPILE_FLAG "-O0 -ggdb" RUNTIME_OUTPUT_DIRECTORY
                                                              "${CMAKE_BINARY_DIR}/bin"
)

add_test(NAME integration_mbedtls_2 COMMAND ${CMAKE_BINARY_DIR}/bin/integration_mbedtls_2
         WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)

# ====================================  Mbedtls 3.x binary ========================================
add_executable(integration_mbedtls_3)
target_link_libraries(integration_mbedtls_3 PRIVATE mbedtls_test target_lib_mb3)
target_link_libraries(integration_mbedtls_3 PRIVATE MbedTLS3::mbedtls)

set_target_properties(
    integration_mbedtls_3 PROPERTIES COMPILE_FLAG "-O0 -ggdb" RUNTIME_OUTPUT_DIRECTORY
                                                              "${CMAKE_BINARY_DIR}/bin"
)

add_test(NAME integration_mbedtls_3 COMMAND ${CMAKE_BINARY_DIR}/bin/integration_mbedtls_3
         WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)

