if (TARGET application OR TARGET host_test OR TARGET sub_ghz_radio)
    # Don't include these files for the bootloader. ESP32 includes them on its own, so we also don't worry about that.
    target_sources(${PROJECT_NAME} PRIVATE
        airborne/cpr_int.c
        airborne/cpr.c
        airborne/nl_int.c
        nasa_cpr_airborne.cpp
    )
    target_include_directories(${PROJECT_NAME} PRIVATE
        .
    )
endif()