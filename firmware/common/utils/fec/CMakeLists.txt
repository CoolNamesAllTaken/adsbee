# Define common source files and include directories
set(FEC_SOURCES
    fec.cpp
    decode_rs_char.c
    encode_rs_char.c
    init_rs_char.c
)

set(FEC_INCLUDE_DIRS .)

# Determine the target based on conditions
if(TARGET host_test)
    set(FEC_TARGET host_test)
elseif(TARGET sub_ghz_radio)
    set(FEC_TARGET ${PROJECT_NAME})
else()
    set(FEC_TARGET application)
endif()

# Apply sources and includes to the determined target
target_sources(${FEC_TARGET} PRIVATE ${FEC_SOURCES})
target_include_directories(${FEC_TARGET} PRIVATE ${FEC_INCLUDE_DIRS})