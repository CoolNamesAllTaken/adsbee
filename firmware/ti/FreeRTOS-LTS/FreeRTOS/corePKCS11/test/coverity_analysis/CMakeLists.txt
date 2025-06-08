# =================================================
# Coverity Analysis Configuration
# =================================================

# Include filepaths for source and include.
include(${MODULE_ROOT_DIR}/pkcsFilePaths.cmake)
include(${MODULE_ROOT_DIR}/tools/mbedtls.cmake)
include(${MODULE_ROOT_DIR}/tools/pkcs11_api.cmake)

# Target for Coverity analysis that builds the library with mbedtls 2.x
add_library(coverity_analysis STATIC)
target_sources(coverity_analysis PRIVATE ${PKCS_SOURCES})
target_link_libraries(coverity_analysis MbedTLS2::mbedcrypto pkcs11_api)

# Build corePKCS11 library with gnuC90 standard due to mbedtls
target_compile_options(coverity_analysis PUBLIC -std=gnu90)

# corePKCS11 public include path.
target_include_directories(
    coverity_analysis
    PUBLIC ${PKCS_INCLUDE_PUBLIC_DIRS}
    PUBLIC ${MBEDTLS_2_INSTALL}/include
    PUBLIC ${MODULE_ROOT_DIR}/source/dependency/3rdparty/mbedtls_utils
    PUBLIC ${MODULE_ROOT_DIR}/test/include
)

# Target for Coverity analysis that builds the library with mbedtls 3.x
add_library(coverity_analysis_mbedtls_3 STATIC)
target_sources(coverity_analysis_mbedtls_3 PRIVATE ${PKCS_SOURCES})
target_link_libraries(coverity_analysis_mbedtls_3 MbedTLS3::mbedcrypto pkcs11_api)

# Build corePKCS11 library with gnuC90 standard due to mbedtls
target_compile_options(coverity_analysis_mbedtls_3 PUBLIC -std=gnu90)

# corePKCS11 public include path.
target_include_directories(
    coverity_analysis_mbedtls_3
    PUBLIC ${PKCS_INCLUDE_PUBLIC_DIRS}
    PUBLIC ${MBEDTLS_3_INSTALL}/include
    PUBLIC ${MODULE_ROOT_DIR}/source/dependency/3rdparty/mbedtls_utils
    PUBLIC ${MODULE_ROOT_DIR}/test/include
)
