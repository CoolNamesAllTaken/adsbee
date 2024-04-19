if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    buffer_utils.cc
    aircraft_dictionary.cc
    ads_b_packet.cc
    # ads_bee.cc # left out since it requires a lot of mocking
    decode_utils.cc
    at_command_parser.cc
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    buffer_utils.cc    
    aircraft_dictionary.cc
    ads_b_packet.cc
    ads_bee.cc
    decode_utils.cc
    at_command_parser.cc
)
endif()