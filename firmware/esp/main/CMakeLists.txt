idf_component_register(
    SRC_DIRS
        "."
        "../../common"
        "../../common/adsb"
        # "../../common/comms" # Currently no src files in here.
        "../../common/coprocessor"
        "../../common/utils"
        "../../common/comms/gdl90"
        "../../common/comms/json"
        "target_test"
    INCLUDE_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/comms"
        "../../common/comms/json"
        "../../common/coprocessor"
        "../../common/utils"
        "target_test"
    EMBED_TXTFILES
        "web/index.html"
        "web/style.css"
        "web/favicon.png"
)

message("PROJECT_SOURCE_DIR: ${PROJECT_SOURCE_DIR}")