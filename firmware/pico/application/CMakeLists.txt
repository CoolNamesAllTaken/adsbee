if (ON_EMBEDDED_DEVICE)
    ## Building for target.
    add_executable(application main.cc)

    add_subdirectory(${ADSBEE_COMMON_DIR} ${CMAKE_BINARY_DIR}/application/adsbee_common)

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
    # pico_add_extra_outputs(application)
    # pico_add_hex_output(application) # temporary workwaround for this bug: https://github.com/raspberrypi/pico-sdk/issues/1829

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
    
    # Build for embedded target
    add_subdirectory(esp32_flasher)
    target_include_directories(application PRIVATE
        ${ADSBEE_MODULES_DIR}/cppAT/src
        .
    )
    target_sources(application PRIVATE
        ${ADSBEE_MODULES_DIR}/cppAT/src/cpp_at.cc
        main.cc # Don't include main for testing.
        ads_bee.cc
        settings.cc
        eeprom.cc
    )

    pico_set_linker_script(application ${APPLICATION_LINKER_SCRIPT})

    # Generated outputs are .elf and .bin. Manually generate .UF2 output to take into account checksum.
    pico_add_bin_output(application)

    # First, we'll create a copy of the original .bin file
    add_custom_command(TARGET application POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy 
                ${CMAKE_CURRENT_BINARY_DIR}/application.bin
                ${CMAKE_CURRENT_BINARY_DIR}/application_original.bin
        COMMENT "Backing up original application binary"
    )

    # Append the CRC32 in application.bin, then turn application.bin into a UF2 file.
    add_custom_command(TARGET application POST_BUILD
        COMMAND ${Python3_EXECUTABLE} ${LINKER_SCRIPTS_DIR}/append_crc32.py
                ${CMAKE_CURRENT_BINARY_DIR}/application.bin
                ${CMAKE_CURRENT_BINARY_DIR}/application.uf2
        COMMENT "Calculating and appending CRC32 to application binary and UF2"
    )

    ## Combined build
    # Turn the bootloader .S file into a linkable object.
    add_library(bootloader_object OBJECT)
    set_source_files_properties(${CMAKE_BINARY_DIR}/bootloader/${BOOTLOADER_SECTION_NAME}.S PROPERTIES
        # Bootloader's boot3.S file is created during build, so don't try finding it during the configuration stage.
        GENERATED TRUE 
    )
    target_sources(bootloader_object PRIVATE 
        ${CMAKE_BINARY_DIR}/bootloader/${BOOTLOADER_SECTION_NAME}.S
    )
    add_dependencies(bootloader_object bootloader)

    add_executable(combined
        $<TARGET_OBJECTS:bootloader_object>
        $<TARGET_PROPERTY:application,SOURCES>
        
    )
    target_include_directories(combined PRIVATE $<TARGET_PROPERTY:application,INCLUDE_DIRECTORIES>)
    target_link_libraries(combined $<TARGET_PROPERTY:application,LINK_LIBRARIES>)
    add_dependencies(combined
        bootloader
        # bootloader_library
        application
    )
    pico_enable_stdio_usb(combined 1) # use USB for standard printing
    pico_enable_stdio_uart(combined 0) # disable STDIO UART

else()
    # Build for testing on host.
    target_include_directories(host_test PRIVATE

    )
    target_sources(host_test PRIVATE

    )
endif()

add_subdirectory(comms)
add_subdirectory(target_test)