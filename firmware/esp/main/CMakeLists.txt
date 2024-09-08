idf_component_register(
    SRC_DIRS
        "."
        "../../common"
        "../../common/adsb"
        # "../../common/comms" # Currently no src files in here.
        "../../common/utils"
        "target_test"
    INCLUDE_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/comms"
        "../../common/utils"
        "target_test"
)
message("PROJECT_SOURCE_DIR: ${PROJECT_SOURCE_DIR}")