if (TARGET application OR TARGET host_test)
    # Set the TARGET_NAME variable so that we only have to do the source and include lists once.
    if (TARGET application)
        set(TARGET_NAME application)
    elseif (TARGET host_test)
        set(TARGET_NAME host_test)
    endif()

    # Don't include these files for the bootloader. ESP32 includes them on its own, so we also don't worry about that.
    target_sources(${TARGET_NAME} PRIVATE
        airborne/cpr_int.c
        airborne/cpr.c
        airborne/nl_int.c
        nasa_cpr_airborne.cpp
    )
    target_include_directories(${TARGET_NAME} PRIVATE
        .
    )
endif()