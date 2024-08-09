if(NOT COMPILED_FOR_TARGET)
    # Build for testing on host.
    target_sources(${PROJECT_NAME} PRIVATE
        # ads_bee.cc # left out since it requires a lot of mocking
    )
else()
    # Build for embedded target
    target_sources(${PROJECT_NAME} PRIVATE 
        ads_bee.cc
        eeprom.cc
        settings.cc
        hal.cc
    )
endif()