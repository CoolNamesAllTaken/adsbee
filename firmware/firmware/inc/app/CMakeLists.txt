if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    buffer_utils.hh
    ads_b_decoder.hh
    ads_b_packet.hh
    # ads_bee.hh
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    buffer_utils.hh
    ads_b_decoder.hh
    ads_b_packet.hh
    # ads_bee.hh
)
endif()