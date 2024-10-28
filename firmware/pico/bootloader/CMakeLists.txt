if (ON_EMBEDDED_DEVICE)
    add_executable(bootloader main.cc)

    add_subdirectory(${ADSBEE_COMMON_DIR} adsbee_common)

    target_include_directories(bootloader PRIVATE 
        ${CMAKE_SOURCE_DIR}/../modules/cppAT/src
    )

    target_sources(bootloader PRIVATE
        ${CMAKE_SOURCE_DIR}/../modules/cppAT/src/cpp_at.cc
    )

    # Firmware: Pull in Pico library
    target_link_libraries(bootloader
        pico_stdlib
        # pico_float # for math functions
        # pico_rand # for generating random numbers
        # hardware_pio
        # hardware_pwm
        # hardware_adc
        hardware_i2c
        hardware_spi
        hardware_exception
        hardware_watchdog
    )

    # Firmware: Create map/bin/hex file etc
    pico_add_extra_outputs(bootloader)
    pico_add_hex_output(bootloader) # temporary workwaround for this bug: https://github.com/raspberrypi/pico-sdk/issues/1829

    # Set up debug USB
    pico_enable_stdio_usb(bootloader 1) # use USB for standard printing
    pico_enable_stdio_uart(bootloader 0) # disable STDIO UART
endif()