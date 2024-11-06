if (ON_EMBEDDED_DEVICE)
    add_executable(bootloader main.cc)

    add_subdirectory(${ADSBEE_COMMON_DIR} ${CMAKE_BINARY_DIR}/bootloader/adsbee_common)

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
        # hardware_i2c
        # hardware_spi
        hardware_exception
        hardware_watchdog
        hardware_dma # for checksums
    )

    pico_add_bin_output(bootloader)

    # Set up debug USB
    pico_enable_stdio_usb(bootloader 1) # use USB for standard printing
    pico_enable_stdio_uart(bootloader 0) # disable STDIO UART

    pico_set_linker_script(bootloader ${BOOTLOADER_LINKER_SCRIPT})

    # Stuff the bootloader.bin output of the build steps above into an assembly file Byte by Byte with the section label
    # boot3, so that it can be linked to a specific section in the linker file for a combined build.
    bin2asm(${CMAKE_CURRENT_BINARY_DIR}/bootloader.bin 
        ${BOOTLOADER_SECTION_NAME} 
        ${CMAKE_CURRENT_BINARY_DIR}/${BOOTLOADER_SECTION_NAME}.S
    )

    # add_library(bootloader_library ${CMAKE_CURRENT_BINARY_DIR}/${BOOTLOADER_SECTION_NAME}.S)

    # # Create a shareable library that is built from boot3.S which can then be linked into other targets.
	# add_library(bootloader_library INTERFACE)
	# add_dependencies(bootloader_library ${BOOTLOADER_SECTION_NAME})
	# # not strictly (or indeed actually) a link library, but this avoids dependency cycle
	# target_link_libraries(bootloader_library INTERFACE ${BOOTLOADER_SECTION_NAME})
endif()