
target_sources(${PROJECT_NAME} PRIVATE
    spi_coprocessor.cc    
    utils/buffer_utils.cc
    utils/data_structures.cc
    adsb/adsb_packet.cc
    adsb/aircraft_dictionary.cc
)
target_include_directories(${PROJECT_NAME} PRIVATE
    adsb
    utils
)