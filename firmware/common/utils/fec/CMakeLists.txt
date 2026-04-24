# Define common source files and include directories
set(FEC_SOURCES
    fec.cpp
    decode_rs_char.c
    encode_rs_char.c
    init_rs_char.c
)

set(FEC_INCLUDE_DIRS .)

# Determine the target(s) based on conditions
if(TARGET host_test OR TARGET host_test_fpu)
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE ${FEC_SOURCES})
            target_include_directories(${_test_tgt} PRIVATE ${FEC_INCLUDE_DIRS})
        endif()
    endforeach()
elseif(TARGET sub_ghz_radio)
    target_sources(${PROJECT_NAME} PRIVATE ${FEC_SOURCES})
    target_include_directories(${PROJECT_NAME} PRIVATE ${FEC_INCLUDE_DIRS})
else()
    target_sources(application PRIVATE ${FEC_SOURCES})
    target_include_directories(application PRIVATE ${FEC_INCLUDE_DIRS})
endif()