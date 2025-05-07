project("core_pkcs11_wrapper_utest")

include(${MODULE_ROOT_DIR}/pkcsFilePaths.cmake)
include(${MODULE_ROOT_DIR}/tools/unity.cmake)
include(${MODULE_ROOT_DIR}/tools/cmock.cmake)
include(${MODULE_ROOT_DIR}/tools/pkcs11_api.cmake)

add_test_target(pkcs11_wrapper_utest "core_pkcs11_utest.c")

target_add_test_runner(pkcs11_wrapper_utest wrapper_utest_config.yml core_pkcs11_utest.c)

target_add_mock_pp(
    pkcs11_wrapper_utest "wrapper_utest_config.yml" "${PKCS11_API_PATH}/pkcs11.h"
    "-include${MODULE_ROOT_DIR}/test/include/pkcs11_defs.h"
)

target_compile_options(
    pkcs11_wrapper_utest PRIVATE "-include${MODULE_ROOT_DIR}/test/include/pkcs11_defs.h"
)

target_include_directories(
    pkcs11_wrapper_utest
    PRIVATE "${CMAKE_CURRENT_LIST_DIR}/include" "${CMAKE_CURRENT_BINARY_DIR}"
            "${MODULE_ROOT_DIR}/source/include" "${MODULE_ROOT_DIR}/test/include"
)

target_add_mock(
    pkcs11_wrapper_utest "wrapper_utest_config.yml"
    "${MODULE_ROOT_DIR}/test/include/malloc_stub.h"
)

target_link_libraries(pkcs11_wrapper_utest PRIVATE cmock pkcs11_api)

add_library(pkcs11_wrapper STATIC)
target_sources(pkcs11_wrapper PRIVATE "${MODULE_ROOT_DIR}/source/core_pkcs11.c")

target_include_directories(
    pkcs11_wrapper PRIVATE "${PKCS11_API_PATH}" "${MODULE_ROOT_DIR}/source/include"
                           "${MODULE_ROOT_DIR}/test/include"
)

target_link_libraries(pkcs11_wrapper PRIVATE pkcs11_api)

target_enable_gcov(pkcs11_wrapper PRIVATE)

target_link_libraries(pkcs11_wrapper_utest PRIVATE pkcs11_wrapper)
