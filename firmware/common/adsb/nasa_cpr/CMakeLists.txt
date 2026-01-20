if (TARGET application)
    # Don't include these files for the bootloader. ESP32 includes them on its own, so we also don't worry about that.
    target_sources(application PRIVATE
        airborne/cpr_int.cpp
        airborne/cpr.cpp
        airborne/nl_int.cpp
        nasa_cpr_airborne.cpp
        nasa_cpr_surface.cpp
        surface/cpr_int.cpp
        surface/cpr.cpp
        surface/nl_int.cpp
    )
    target_include_directories(application PRIVATE
        .
    )
elseif(TARGET host_test)
    target_sources(host_test PRIVATE
        airborne/cpr_int.cpp
        airborne/cpr.cpp
        airborne/nl_int.cpp
        nasa_cpr_airborne.cpp
        nasa_cpr_surface.cpp
        surface/cpr_int.cpp
        surface/cpr.cpp
        surface/nl_int.cpp
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()