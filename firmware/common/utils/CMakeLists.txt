
if (TARGET application)
    add_subdirectory(fec)
    target_sources(application PRIVATE
        buffer_utils.cpp
        cpu_utils.cpp
        data_structures.cpp
        crc/crc.cpp
        geo/geo_utils.cpp
    )
    target_include_directories(application PRIVATE
        .
        crc
        geo
    )
elseif (TARGET bootloader)
    target_include_directories(bootloader PRIVATE
        . # We just want hal.hh for now.
    )
elseif (TARGET sub_ghz_radio)
    add_subdirectory(fec)
    target_sources(sub_ghz_radio PRIVATE
        buffer_utils.cpp
        cpu_utils.cpp
        data_structures.cpp
        crc/crc.cpp
    )
    target_include_directories(sub_ghz_radio PRIVATE
        .
        crc
        geo
        rs
    )
elseif (TARGET host_test)
    add_subdirectory(fec)
    target_sources(host_test PRIVATE
        buffer_utils.cpp
        cpu_utils.cpp
        data_structures.cpp
        crc/crc.cpp
        geo/geo_utils.cpp
    )
    target_include_directories(host_test PRIVATE
        .
        crc
        geo
        rs
    )
endif()
