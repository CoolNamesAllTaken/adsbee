if (ON_EMBEDDED_DEVICE)
    ## Building for target.
    add_executable(application main.cc)

    if(CMAKE_BUILD_TYPE STREQUAL "Debug")
        # set(PICO_DEOPTIMIZED_DEBUG 1)
        add_compile_definitions(HARDWARE_UNIT_TESTS)
    endif()

    # Create C header file with the name <pio program>.pio.h
    pico_generate_pio_header(application  
        ${CMAKE_CURRENT_LIST_DIR}/pio/capture.pio       
    )

    # Firmware: Pull in Pico library
    target_link_libraries(application 
        pico_stdlib
        pico_float # for math functions
        pico_rand # for generating random numbers
        hardware_pio
        hardware_pwm
        hardware_adc
        hardware_i2c
        hardware_spi
        hardware_exception
        hardware_watchdog
    )

    # Firmware: Create map/bin/hex file etc
    pico_add_extra_outputs(application)
    pico_add_hex_output(application) # temporary workwaround for this bug: https://github.com/raspberrypi/pico-sdk/issues/1829

    # Set up debug USB
    pico_enable_stdio_usb(application 1) # use USB for standard printing
    pico_enable_stdio_uart(application 0) # disable STDIO UART

    ## ESP32 Serial Flasher
    # Set parameters for serial flasher.
    # NOTE: These are mirrored in the top level `pico/.vscode/c_cpp_properties.json` for intellisense.
    add_compile_definitions(
        MD5_ENABLED 
        SERIAL_FLASHER_INTERFACE_UART 
        SERIAL_FLASHER_DEBUG_TRACE=0 
        SERIAL_FLASHER_WRITE_BLOCK_RETRIES=3
    )

    # Embed binaries into the app.
    # In ESP-IDF this can also be done using EMBED_FILES option of idf_component_register.
    # Here an external tool is used to make file embedding similar with other ports.
    include(${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin2array.cmake)
    # Create a file dependency that copies over the most recently built ESP32 firmware binary to the bin directory used by
    # esp32_flasher. Re-runs cmake if the file gets changed.
    # For some reason putting binaries.c in the build folder never works out. Put it in the esp32_flasher bin directory
    # instead.
    configure_file(${CMAKE_SOURCE_DIR}/../esp/build/adsbee_esp.bin ${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin/adsbee_esp.bin COPYONLY)
    create_resources(${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin ${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin/binaries.c)
    set_property(SOURCE ${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin/binaries.c PROPERTY GENERATED 1)
    target_sources(application PRIVATE ${CMAKE_CURRENT_LIST_DIR}/esp32_flasher/bin/binaries.c)
    

else()
    set(CMAKE_BUILD_TYPE "Debug") # Now that we've identified we're running tests, revert to an actual build config.

    add_compile_options(
        -Wall                # Include all warnings.
        -Wno-format          # int != int32_t as far as the compiler is concerned because gcc has int32_t as long int
        -Wno-unused-function # we have some for the docs that aren't called
        -Wno-maybe-uninitialized
    )

    add_subdirectory(${CMAKE_SOURCE_DIR}/host_test)

    target_include_directories(host_test PRIVATE
        ../common
        /ads_bee/modules/googletest
        /ads_bee/modules/cppAT/src
        src
        host_test
    )

    target_sources(host_test PRIVATE
        /ads_bee/modules/cppAT/src/cpp_at.cc
        /ads_bee/modules/cppAT/test/test_cpp_at.cc
    )

    # Test: Pull in google test library
    add_library(libgtest SHARED IMPORTED)
    set_target_properties(libgtest PROPERTIES IMPORTED_LOCATION /ads_bee/modules/googletest/build/lib/libgtest.so)
    target_link_libraries(host_test PRIVATE libgtest)
    

endif()

if(ON_EMBEDDED_DEVICE)
    # Build for embedded target
    add_subdirectory(esp32_flasher)
    target_include_directories(application PRIVATE
        ${CMAKE_SOURCE_DIR}/../modules/cppAT/src
        .
    )
    target_sources(application PRIVATE
        ${CMAKE_SOURCE_DIR}/../modules/cppAT/src/cpp_at.cc
        main.cc # Don't include main for testing.
        ads_bee.cc
        settings.cc
        eeprom.cc
    )
else()
    # Build for testing on host.
    target_include_directories(host_test PRIVATE

    )
    target_sources(host_test PRIVATE
        ads_bee.cc
        settings.cc
    )
endif()

add_subdirectory(comms)
add_subdirectory(target_test)