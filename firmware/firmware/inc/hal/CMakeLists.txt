if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    hal.hh
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    hal.hh
)
endif()