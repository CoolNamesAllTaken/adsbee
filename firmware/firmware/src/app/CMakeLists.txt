if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    buffer_utils.cc
    # ads_b_decoder.cc
    aircraft_dictionary.cc
    ads_b_packet.cc
    # ads_bee.cc
    decode_utils.cc
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    buffer_utils.cc    
    # ads_b_decoder.cc
    aircraft_dictionary.cc
    ads_b_packet.cc
    # ads_bee.cc
    decode_utils.cc
)
endif()