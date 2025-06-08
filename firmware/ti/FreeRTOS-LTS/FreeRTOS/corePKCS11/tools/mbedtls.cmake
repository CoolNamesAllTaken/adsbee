include(FetchContent)

set(FETCHCONTENT_QUIET OFF)

set(MBEDTLS_2_VERSION 2.28.8)

FetchContent_Declare(
    mbedtls_2
    GIT_REPOSITORY "https://github.com/Mbed-TLS/mbedtls"
    GIT_TAG v${MBEDTLS_2_VERSION}
    PATCH_COMMAND ${MODULE_ROOT_DIR}/tools/mbedtls_configure.sh <SOURCE_DIR> config.h
)

FetchContent_GetProperties(
    mbedtls_2
    POPULATED mbedtls_2_POPULATED
)

if(NOT ${mbedtls_2_POPULATED})
    FetchContent_Populate(mbedtls_2)
endif()

if(NOT TARGET MbedTLS2_mbedtls)
    set(MBEDTLS_2_BIN_DIR ${CMAKE_CURRENT_BINARY_DIR}/lib/mbedtls_2)
    set(MBEDTLS_TARGET_PREFIX "MbedTLS2_")

    option(USE_STATIC_MBEDTLS_LIBRARY "" ON)
    option(USE_SHARED_MBEDTLS_LIBRARY "" OFF)
    option(ENABLE_PROGRAMS "" OFF)
    option(ENABLE_TESTING "" OFF)

    add_subdirectory(${mbedtls_2_SOURCE_DIR} ${mbedtls_2_BINARY_DIR})

    add_library(MbedTLS2_interface INTERFACE)
    get_target_property(mbedtls_includes MbedTLS2_mbedtls INCLUDE_DIRECTORIES)
    target_include_directories(
        MbedTLS2_interface
        INTERFACE ${mbedtls_includes}
        INTERFACE ${mbedtls_2_SOURCE_DIR}/library
        INTERFACE ${mbedtls_2_SOURCE_DIR}/include/mbedtls
    )

    set_target_properties(
        MbedTLS2_mbedcrypto MbedTLS2_mbedtls MbedTLS2_mbedx509
        PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${MBEDTLS_2_BIN_DIR} LIBRARY_OUTPUT_DIRECTORY
                                                                 ${MBEDTLS_2_BIN_DIR}
    )

    add_library(MbedTLS2::mbedtls ALIAS MbedTLS2_mbedtls)
    add_library(MbedTLS2::mbedcrypto ALIAS MbedTLS2_mbedcrypto)
    add_library(MbedTLS2::mbedx509 ALIAS MbedTLS2_mbedx509)
    add_library(MbedTLS2::interface ALIAS MbedTLS2_interface)
endif()

set(MBEDTLS_3_VERSION 3.6.0)

FetchContent_Declare(
    mbedtls_3
    GIT_REPOSITORY "https://github.com/Mbed-TLS/mbedtls"
    GIT_TAG v${MBEDTLS_3_VERSION}
    PATCH_COMMAND
        ${CMAKE_CURRENT_LIST_DIR}/mbedtls_configure.sh <SOURCE_DIR> mbedtls_config.h
)

FetchContent_GetProperties(
    mbedtls_3
    POPULATED mbedtls_3_POPULATED
)

if(NOT ${mbedtls_3_POPULATED})
    FetchContent_Populate(mbedtls_3)
endif()

if(NOT TARGET MbedTLS3_mbedtls)
    set(MBEDTLS_3_BIN_DIR ${CMAKE_CURRENT_BINARY_DIR}/lib/mbedtls_3)
    set(MBEDTLS_TARGET_PREFIX "MbedTLS3_")

    option(USE_STATIC_MBEDTLS_LIBRARY "" ON)
    option(USE_SHARED_MBEDTLS_LIBRARY "" OFF)
    option(ENABLE_PROGRAMS "" OFF)
    option(ENABLE_TESTING "" OFF)

    add_subdirectory(${mbedtls_3_SOURCE_DIR} ${mbedtls_3_BINARY_DIR})

    add_library(MbedTLS3_interface INTERFACE)
    get_target_property(mbedtls_includes MbedTLS3_mbedtls INCLUDE_DIRECTORIES)
    target_include_directories(
        MbedTLS3_interface
        INTERFACE ${mbedtls_includes}
        INTERFACE ${mbedtls_3_SOURCE_DIR}/library
        INTERFACE ${mbedtls_3_SOURCE_DIR}/include/mbedtls
    )

    set_target_properties(
        MbedTLS3_mbedcrypto MbedTLS3_mbedtls MbedTLS3_mbedx509
        PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${MBEDTLS_3_BIN_DIR} LIBRARY_OUTPUT_DIRECTORY
                                                                 ${MBEDTLS_3_BIN_DIR}
    )

    add_library(MbedTLS3::mbedtls ALIAS MbedTLS3_mbedtls)
    add_library(MbedTLS3::mbedcrypto ALIAS MbedTLS3_mbedcrypto)
    add_library(MbedTLS3::mbedx509 ALIAS MbedTLS3_mbedx509)
    add_library(MbedTLS3::interface ALIAS MbedTLS3_interface)
endif()
