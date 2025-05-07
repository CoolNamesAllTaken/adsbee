cmake_minimum_required(VERSION 3.13.0)
project( "corePKCS11 tests"
         VERSION 3.6.1
         LANGUAGES C)

# Allow the project to be organized into folders.
set_property(GLOBAL PROPERTY USE_FOLDERS ON)
set_directory_properties(PROPERTIES EP_PREFIX "${CMAKE_BINARY_DIR}/_deps")

# Do not allow in-source build.
if(${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR})
    message(
        FATAL_ERROR
            "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build."
    )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
set(MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "corePKCS11 repository root.")

option(SYSTEM_TESTS "Set this to ON to build system tests" ON)
option(UNITTEST "Set this to ON to build unit tests" ON)
option(COV_ANALYSIS "Set this to ON to build coverity_analysis target" ON)

# Set output directories.
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

include(${MODULE_ROOT_DIR}/tools/mbedtls.cmake)

if(UNITTEST OR SYSTEM_TESTS)
    include(${MODULE_ROOT_DIR}/tools/unity.cmake)
    include(${MODULE_ROOT_DIR}/tools/cmock.cmake)
endif()

# ========================================
# Test Configuration
# ========================================

# Define a CMock resource path.
set(
    CMOCK_DIR
    ${MODULE_ROOT_DIR}/test/unit-test/CMock
    CACHE INTERNAL
        "CMock library source directory."
)

# Use CTest utility for managing test runs. This has to be added BEFORE defining test targets with
# add_test()
enable_testing()

if(UNITTEST)
    add_subdirectory(pkcs11_mbedtls_utest)
    add_subdirectory(pkcs11_utils_utest)
    add_subdirectory(wrapper_utest)
endif()

if(SYSTEM_TESTS)
    add_subdirectory(mbedtls_integration)
endif()

if(COV_ANALYSIS)
    add_subdirectory(coverity_analysis)
endif()

# ========================================
# Coverage Analysis configuration
# ========================================

if(UNITTEST OR SYSTEM_TESTS)
    # Add a target for running coverage on tests.
    add_custom_target(
        coverage
        COMMAND ${CMAKE_COMMAND} -P ${MODULE_ROOT_DIR}/tools/cmock/coverage.cmake
        DEPENDS cmock
                unity
                $<$<TARGET_EXISTS:core_pkcs11_mbedtls_utest>:core_pkcs11_mbedtls_utest>
                $<$<TARGET_EXISTS:pkcs11_wrapper_utest>:pkcs11_wrapper_utest>
                $<$<TARGET_EXISTS:pkcs11_utils_utest>:pkcs11_utils_utest>
                $<$<TARGET_EXISTS:integration_mbedtls_2>:integration_mbedtls_2>
                $<$<TARGET_EXISTS:integration_mbedtls_3>:integration_mbedtls_3>
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()
