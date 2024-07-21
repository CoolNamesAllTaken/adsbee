if(NOT COMPILED_FOR_TARGET)
    # Build for testing on host.
    target_sources(ads_bee_test PRIVATE
        # comms.cc
    )
    target_include_directories(${PROJECT_NAME} PRIVATE
        beast_utils.hh
    )
else()
    # Build for embedded target
    target_sources(ads_bee PRIVATE
        
    )
    target_include_directories(${PROJECT_NAME} PRIVATE
        beast_utils.hh
    )
endif()