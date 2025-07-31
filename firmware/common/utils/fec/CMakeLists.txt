if (TARGET sub_ghz_radio)
    # Don't include these files for the bootloader. ESP32 includes them on its own, so we also don't worry about that.
    target_sources(${PROJECT_NAME} PRIVATE
        fec.cpp
        decode_rs_char.c
        init_rs_char.c
    )
    target_include_directories(${PROJECT_NAME} PRIVATE
        .
    )
elseif(TARGET host_test)
    target_sources(host_test PRIVATE
        fec.cpp
        decode_rs_char.c
        init_rs_char.c
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()