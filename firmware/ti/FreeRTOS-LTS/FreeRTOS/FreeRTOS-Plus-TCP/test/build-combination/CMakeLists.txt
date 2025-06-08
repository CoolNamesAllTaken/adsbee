# Select the appropriate Build Test configuration
set(FREERTOS_PLUS_TCP_TEST_CONFIGURATION "CUSTOM" CACHE STRING "FreeRTOS Plus TCP Build Test configuration")
set(FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST
    CUSTOM                  # Custom (external) configuration -eg from a top-level project
    ENABLE_ALL              # Enable all configuration settings
    ENABLE_ALL_IPV4         # Enable all configuration settings IPv4 UDP
    ENABLE_ALL_IPV6         # Enable all configuration settings IPv6 UDP
    ENABLE_ALL_IPV4_TCP     # Enable all configuration settings IPv4 TCP
    ENABLE_ALL_IPV6_TCP     # Enable all configuration settings IPv6 TCP
    ENABLE_ALL_IPV4_IPV6    # Enable all configuration settings IPv4 IPv6 UDP
    DISABLE_ALL             # Disable all configuration settings
    HEADER_SELF_CONTAIN     # Enable header self contain test
    DEFAULT_CONF            # Default (typical) configuration
)
if(NOT FREERTOS_PLUS_TCP_TEST_CONFIGURATION IN_LIST FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST)
    message(FATAL_ERROR "Invalid FREERTOS_PLUS_TCP_TEST_CONFIGURATION value '${FREERTOS_PLUS_TCP_TEST_CONFIGURATION}' should be one of: ${FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST}")
else()
    message(STATUS "Using FreeRTOS-Plus-TCP Test Configuration : ${FREERTOS_PLUS_TCP_TEST_CONFIGURATION}")
    if (NOT FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "CUSTOM")
        message(WARNING "FreeRTOS-Kernel configuration settings are configured by FreeRTOS-Plus-TCP")
    endif()
endif()

add_library( freertos_plus_tcp_config_common INTERFACE )
target_include_directories(freertos_plus_tcp_config_common INTERFACE Common )

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_disable INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_disable INTERFACE AllDisable)
target_link_libraries(freertos_plus_tcp_config_all_disable INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable INTERFACE AllEnable)
target_link_libraries(freertos_plus_tcp_config_all_enable INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable_ipv4 INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable_ipv4 INTERFACE Enable_IPv4)
target_link_libraries(freertos_plus_tcp_config_all_enable_ipv4 INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable_ipv6 INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable_ipv6 INTERFACE Enable_IPv6)
target_link_libraries(freertos_plus_tcp_config_all_enable_ipv6 INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable_ipv4_ipv6 INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable_ipv4_ipv6 INTERFACE Enable_IPv4_IPv6)
target_link_libraries(freertos_plus_tcp_config_all_enable_ipv4_ipv6 INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable_ipv4_tcp INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable_ipv4_tcp INTERFACE Enable_IPv4_TCP)
target_link_libraries(freertos_plus_tcp_config_all_enable_ipv4_tcp INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable_ipv6_tcp INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable_ipv6_tcp INTERFACE Enable_IPv6_TCP)
target_link_libraries(freertos_plus_tcp_config_all_enable_ipv6_tcp INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_header_self_contain INTERFACE)
target_include_directories(freertos_plus_tcp_config_header_self_contain INTERFACE Header_Self_Contain)
target_link_libraries(freertos_plus_tcp_config_header_self_contain INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_default INTERFACE)
target_include_directories(freertos_plus_tcp_config_default INTERFACE DefaultConf)
target_link_libraries(freertos_plus_tcp_config_default INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
# Configuration for FreeRTOS-Kernel
if(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "CUSTOM" )
    # Check Config target is available. And then do nothing.
    if(NOT TARGET freertos_config )
        message(FATAL_ERROR "FREERTOS_PLUS_TCP_TEST_CONFIGURATION = CUSTOM, but no freertos_config target defined.")
    endif()
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "DISABLE_ALL" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_disable)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL_IPV4" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable_ipv4)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL_IPV6" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable_ipv6)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL_IPV4_TCP" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable_ipv4_tcp)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL_IPV6_TCP" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable_ipv6_tcp)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL_IPV4_IPV6" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable_ipv4_ipv6)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "HEADER_SELF_CONTAIN" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_header_self_contain)
    include( Header_Self_Contain/headerSelfContain.cmake )
else()
    add_library( freertos_config ALIAS freertos_plus_tcp_config_default)
endif()

# FreeRTOS-Plus-TCP compilation options configuration
set_property(TARGET freertos_plus_tcp PROPERTY C_STANDARD 90)
target_compile_options(freertos_plus_tcp
    PRIVATE

    ### Gnu/Clang C Options
    $<$<COMPILE_LANG_AND_ID:C,GNU>:-fdiagnostics-color=always>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-fcolor-diagnostics>

    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wall>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wextra>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Werror>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wpedantic>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wconversion>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wunused-variable>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Weverything>

    # Suppressions required to build clean with clang.
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-qual>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-switch-enum>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-declaration-after-statement>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-covered-switch-default>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-extra-semi-stmt>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align>
)

# Common build combination test.
add_executable(freertos_plus_tcp_build_test EXCLUDE_FROM_ALL)

target_sources(freertos_plus_tcp_build_test
PRIVATE
    Common/main.c
)

target_compile_options(freertos_plus_tcp_build_test
    PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-qual>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-format-nonliteral>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-implicit-function-declaration>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-prototypes>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-reserved-identifier>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-shorten-64-to-32>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-sign-conversion>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-parameter>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-variable>
)

set( FREERTOS_HEAP "4" CACHE STRING "" FORCE)

target_link_libraries(freertos_plus_tcp_build_test
    PRIVATE
    freertos_plus_tcp
    freertos_kernel
)
