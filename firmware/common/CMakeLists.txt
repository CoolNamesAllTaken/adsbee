
if (TARGET application)
    # Primary RP2040 application.
    add_subdirectory(adsb/nasa_cpr)
    target_sources(application PRIVATE
        # NOTE: Annoyingly, all source files need to end with .c or .cpp to be seen by the ESP IDF.
        settings/settings_strs.cpp
        settings/settings.cpp
        comms/gdl90/gdl90_utils.cpp
        comms/mavlink/mavlink_utils.cpp
        comms/raw/raw_utils.cpp
        utils/buffer_utils.cpp
        utils/data_structures.cpp
        utils/crc/crc.cpp
        utils/geo/geo_utils.cpp
        adsb/transponder_packet.cpp
        adsb/aircraft_dictionary.cpp
        adsb/decode_utils.cpp
        adsb/packet_decoder.cc
        coprocessor/spi_coprocessor.cpp
        coprocessor/object_dictionary.cpp
        firmware_update/firmware_update.cc
        firmware_update/flash_utils.cc
    )
    target_include_directories(application PRIVATE
        .
        adsb
        utils
        utils/crc
        utils/geo
        comms
        comms/beast
        comms/csbee
        comms/gdl90
        comms/json
        comms/mavlink
        comms/raw
        coprocessor
        firmware_update
        settings
    )
elseif (TARGET bootloader)
    # RP2040 bootloader.
    target_sources(bootloader PRIVATE
        firmware_update/firmware_update.cc
        firmware_update/flash_utils.cc
    )
    target_include_directories(bootloader PRIVATE
        utils # We just want hal.hh for now.
        firmware_update
        
    )
elseif (TARGET sub_ghz_radio)
    # TI CC1312R sub-GHz radio.
    add_subdirectory(adsb/nasa_cpr)
    target_sources(${PROJECT_NAME} PRIVATE
        settings/settings_strs.cpp
        settings/settings.cpp
        utils/buffer_utils.cpp
        utils/data_structures.cpp
        utils/crc/crc.cpp
        # adsb/transponder_packet.cpp
        # adsb/aircraft_dictionary.cpp
        adsb/decode_utils.cpp
        coprocessor/spi_coprocessor.cpp
        coprocessor/object_dictionary.cpp
    )
    target_include_directories(${PROJECT_NAME} PRIVATE
        # adsb
        comms
        comms/json # Not actually used, but added to avoid compile errors.
        coprocessor
        settings
        utils
        utils/crc
        utils/geo
        utils/rs
    )
elseif (TARGET host_test)
    # Off-target unit testing.
    add_subdirectory(adsb/nasa_cpr)
    target_sources(host_test PRIVATE
        adsb/transponder_packet.cpp
        adsb/aircraft_dictionary.cpp
        adsb/decode_utils.cpp
        adsb/packet_decoder.cc
        comms/gdl90/gdl90_utils.cpp
        comms/raw/raw_utils.cpp
        coprocessor/spi_coprocessor.cpp
        coprocessor/object_dictionary.cpp
        settings/settings_strs.cpp
        settings/settings.cpp
        utils/buffer_utils.cpp
        utils/data_structures.cpp
        utils/crc/crc.cpp
        utils/geo/geo_utils.cpp
    )
    target_include_directories(host_test PRIVATE
        adsb
        comms/beast
        comms/csbee
        comms/gdl90
        comms/json
        comms/raw
        coprocessor
        utils
        utils/crc
        utils/geo
        settings
    )
endif()