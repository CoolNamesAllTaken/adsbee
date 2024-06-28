if(CROSS_COMPILED)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE
    /ads_bee/common/buffer_utils.cc
    /ads_bee/common/data_structures.cc
)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    /ads_bee/common/buffer_utils.cc    
    /ads_bee/common/data_structures.cc
)
endif()