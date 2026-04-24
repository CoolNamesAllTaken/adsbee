
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
elseif (TARGET host_test OR TARGET host_test_fpu)
    add_subdirectory(fec)
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE
                buffer_utils.cpp
                cpu_utils.cpp
                data_structures.cpp
                crc/crc.cpp
                geo/geo_utils.cpp
            )
            target_include_directories(${_test_tgt} PRIVATE
                .
                crc
                geo
                rs
            )
        endif()
    endforeach()
endif()
