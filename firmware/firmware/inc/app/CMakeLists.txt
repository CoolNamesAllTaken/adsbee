if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    ads_b_decoder.hh
    # ads_bee.hh
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    ads_b_decoder.hh
    # ads_bee.hh
)
endif()