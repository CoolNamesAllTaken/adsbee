if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    comms_at.cc
    comms.cc
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    comms_at.cc
    comms.cc
)
endif()