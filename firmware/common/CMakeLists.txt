
target_sources(${PROJECT_NAME} PRIVATE
# NOTE: Annoyingly, all source files need to end with .c or .cpp to be seen by the ESP IDF.
    settings_strs.cpp
    utils/buffer_utils.cpp
    utils/data_structures.cpp
    adsb/transponder_packet.cpp
    adsb/aircraft_dictionary.cpp
    adsb/decode_utils.cpp
    coprocessor/spi_coprocessor.cpp
    coprocessor/object_dictionary.cpp
)
target_include_directories(${PROJECT_NAME} PRIVATE
    adsb
    utils
    comms
    comms/beast
    comms/csbee
    coprocessor
)