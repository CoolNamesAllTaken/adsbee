
if (TARGET application)
    add_subdirectory(nasa_cpr)
    target_sources(application PRIVATE
        mode_s_packet.cpp
        uat_packet.cpp
        aircraft_dictionary.cpp
        decode_utils.cpp
        mode_s_packet_decoder.cc
    )
    target_include_directories(application PRIVATE
        .
    )
elseif (TARGET sub_ghz_radio)
    add_subdirectory(nasa_cpr)
    target_sources(sub_ghz_radio PRIVATE
        # adsb/mode_s_packet.cpp
        uat_packet.cpp
        # adsb/aircraft_dictionary.cpp
        decode_utils.cpp
    )
    target_include_directories(sub_ghz_radio PRIVATE
        .
    )
elseif (TARGET host_test)
    add_subdirectory(nasa_cpr)
    target_sources(host_test PRIVATE
        mode_s_packet.cpp
        uat_packet.cpp
        aircraft_dictionary.cpp
        decode_utils.cpp
        mode_s_packet_decoder.cc
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()
