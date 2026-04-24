
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
elseif (TARGET host_test OR TARGET host_test_fpu)
    add_subdirectory(nasa_cpr)
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE
                mode_s_packet.cpp
                uat_packet.cpp
                aircraft_dictionary.cpp
                decode_utils.cpp
                mode_s_packet_decoder.cc
            )
            target_include_directories(${_test_tgt} PRIVATE
                .
            )
        endif()
    endforeach()
endif()
