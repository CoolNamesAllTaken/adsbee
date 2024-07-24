idf_component_register(
    # SRCS
    #     "app_main.cc"
    #     "../../../../common/spi_coprocessor.cc"
    SRC_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/utils"
    INCLUDE_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/utils"
    # EMBED_TXTFILES
)
message("PROJECT_SOURCE_DIR: ${PROJECT_SOURCE_DIR}")
# add_subdirectory(../../..)
# component_add