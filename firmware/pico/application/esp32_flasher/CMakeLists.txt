if(ON_EMBEDDED_DEVICE)
    # NOTE: Don't add compile definitions here, as they won't be bubbled up to the top level CMakeLists.txt, since this
    # is included with add_subdirectory() and not include().

    file(GLOB SRC_FILES "esp_serial_flasher/*.c")
    target_sources(application PRIVATE
        ${SRC_FILES}
        bin/binaries.c
        esp32_flasher.cc
    )

    # Don't deal with any of this for unit testing on the host.
    target_include_directories(application PRIVATE
        .
    )

endif()