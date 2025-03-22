if(ON_EMBEDDED_DEVICE)
    # Build for embedded target
    target_sources(application PRIVATE
        hardware_unit_tests.cc
        test_clocks.cc
        test_eeprom.cc
        test_spi_coprocessor.cc
        test_flash.cc
    )
    target_include_directories(application PRIVATE
        .
    )
else()
    # Build for testing on host.
    target_sources(host_test PRIVATE

    )
    target_include_directories(host_test PRIVATE
        
    )
endif()