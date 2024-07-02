if(NOT COMPILED_FOR_TARGET)
# Build for testing on host.
target_sources(${PROJECT_NAME} PRIVATE
    # ads_bee.cc # left out since it requires a lot of mocking
    decode_utils.cc
)
else()
# Build for embedded target
target_sources(${PROJECT_NAME} PRIVATE 
    ads_bee.cc
    decode_utils.cc
    eeprom.cc
    settings.cc
)
endif()