if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    buffer_utils.cc
    data_structures.cc
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    buffer_utils.cc    
    data_structures.cc
)
endif()