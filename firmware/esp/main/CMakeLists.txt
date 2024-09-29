idf_component_register(
    SRC_DIRS
        "."
        "../../common"
        "../../common/adsb"
        # "../../common/comms" # Currently no src files in here.
        "../../common/coprocessor"
        "../../common/utils"
        "../../common/comms/gdl90"
        "target_test"
    INCLUDE_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/comms"
        "../../common/coprocessor"
        "../../common/utils"
        "target_test"
)
message("PROJECT_SOURCE_DIR: ${PROJECT_SOURCE_DIR}")