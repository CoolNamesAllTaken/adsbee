
target_sources(${PROJECT_NAME} PRIVATE
# NOTE: Annoyingly, all source files need to end with .c or .cpp to be seen by the ESP IDF.
    spi_coprocessor.cpp    
    utils/buffer_utils.cpp
    utils/data_structures.cpp
    adsb/transponder_packet.cpp
    adsb/aircraft_dictionary.cpp
    adsb/decode_utils.cpp
)
target_include_directories(${PROJECT_NAME} PRIVATE
    adsb
    utils
    comms
    comms/beast
)