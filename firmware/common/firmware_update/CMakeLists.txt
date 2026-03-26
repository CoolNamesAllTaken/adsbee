
if (TARGET application)
    target_sources(application PRIVATE
        firmware_update.cc
        flash_utils.cc
    )
    target_include_directories(application PRIVATE
        .
    )
elseif (TARGET bootloader)
    target_sources(bootloader PRIVATE
        firmware_update.cc
        flash_utils.cc
    )
    target_include_directories(bootloader PRIVATE
        .
    )
endif()
