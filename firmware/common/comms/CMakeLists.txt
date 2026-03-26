
if (TARGET application)
    target_sources(application PRIVATE
        comms_reporting.cpp
        beast/beast_utils.cpp
        gdl90/gdl90_utils.cpp
        mavlink/mavlink_utils.cpp
        raw/raw_utils.cpp
    )
    target_include_directories(application PRIVATE
        .
        beast
        csbee
        gdl90
        json
        mavlink
        raw
    )
elseif (TARGET sub_ghz_radio)
    target_include_directories(sub_ghz_radio PRIVATE
        .
        json # Not actually used, but added to avoid compile errors.
    )
elseif (TARGET host_test)
    target_sources(host_test PRIVATE
        beast/beast_utils.cpp
        gdl90/gdl90_utils.cpp
        raw/raw_utils.cpp
    )
    target_include_directories(host_test PRIVATE
        beast
        csbee
        gdl90
        json
        mavlink
        raw
    )
endif()
