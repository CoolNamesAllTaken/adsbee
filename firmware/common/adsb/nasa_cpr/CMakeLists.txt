if (TARGET application)
    # Don't include these files for the bootloader. ESP32 includes them on its own, so we also don't worry about that.
    target_sources(application PRIVATE
        airborne/cpr_int.c
        airborne/cpr.c
        airborne/nl_int.c
        nasa_cpr_airborne.cpp
    )
    target_include_directories(application PRIVATE
        .
    )
elseif(TARGET host_test)
    target_sources(host_test PRIVATE
        airborne/cpr_int.c
        airborne/cpr.c
        airborne/nl_int.c
        nasa_cpr_airborne.cpp
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()