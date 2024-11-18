
if (TARGET application)
    target_sources(application PRIVATE
        # NOTE: Annoyingly, all source files need to end with .c or .cpp to be seen by the ESP IDF.
        settings_strs.cpp
        comms/gdl90/gdl90_utils.cpp
        utils/buffer_utils.cpp
        utils/data_structures.cpp
        adsb/transponder_packet.cpp
        adsb/aircraft_dictionary.cpp
        adsb/decode_utils.cpp
        coprocessor/spi_coprocessor.cpp
        coprocessor/object_dictionary.cpp
    )
    target_include_directories(application PRIVATE
        .
        adsb
        utils
        comms
        comms/beast
        comms/csbee
        comms/gdl90
        comms/json
        coprocessor
    )
elseif (TARGET bootloader)
    target_sources(bootloader PRIVATE
        
    )
    target_include_directories(bootloader PRIVATE
        utils # We just want hal.hh for now.
    )
elseif (TARGET host_test)
    target_sources(host_test PRIVATE
        settings_strs.cpp
        comms/gdl90/gdl90_utils.cpp
        utils/buffer_utils.cpp
        utils/data_structures.cpp
        adsb/transponder_packet.cpp
        adsb/aircraft_dictionary.cpp
        adsb/decode_utils.cpp
        coprocessor/spi_coprocessor.cpp
        coprocessor/object_dictionary.cpp
    )
    target_include_directories(host_test PRIVATE
        adsb
        comms/beast
        comms/csbee
        comms/gdl90
        comms/json
        coprocessor
        utils
    )
endif()