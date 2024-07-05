if(NOT COMPILED_FOR_TARGET)
# Build for testing on host.
target_sources(ads_bee_test PRIVATE

)
else()
# Build for embedded target
target_sources(ads_bee PRIVATE
    hardware_unit_tests.cc
    test_eeprom.cc
)
endif()