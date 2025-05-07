include(FetchContent)

FetchContent_Declare(
    pkcs11_api GIT_REPOSITORY https://github.com/oasis-tcs/pkcs11.git GIT_TAG 2-40-errata-1
)

FetchContent_GetProperties(
    pkcs11_api
    POPULATED pkcs11_api_POPULATED
    SOURCE_DIR pkcs11_api_SOURCE_DIR
)

if(NOT ${pkcs11_api_POPULATED})
    FetchContent_Populate(pkcs11_api)
endif()

set(PKCS11_API_PATH ${pkcs11_api_SOURCE_DIR}/published/2-40-errata-1)

if(NOT TARGET pkcs11_api)
    add_library(pkcs11_api INTERFACE)
    target_include_directories(pkcs11_api INTERFACE ${PKCS11_API_PATH})
endif()
