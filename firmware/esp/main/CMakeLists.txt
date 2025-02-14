idf_component_register(
    SRC_DIRS
        "."
        # "../../common"
        "../../common/adsb"
        "../../common/adsb/nasa_cpr"
        "../../common/adsb/nasa_cpr/airborne"
        "../../common/adsb/nasa_cpr/coarse"
        "../../common/adsb/nasa_cpr/surface"
        "../../common/adsb/nasa_cpr/intent"
        # "../../common/comms" # Currently no src files in here.
        "../../common/coprocessor"
        "../../common/utils"
        "../../common/utils/crc"
        "../../common/comms/gdl90"
        "../../common/comms/json"
        "../../common/settings"
        "target_test"
    INCLUDE_DIRS
        "."
        "../../common"
        "../../common/adsb"
        "../../common/adsb/nasa_cpr"
        "../../common/comms"
        "../../common/comms/json"
        "../../common/coprocessor"
        "../../common/utils"
        "../../common/utils/crc"
        "../../common/settings"
        "target_test"
    EMBED_TXTFILES
        "web/index.html"
        "web/style.css"
        "web/favicon.png"
)

message("PROJECT_SOURCE_DIR: ${PROJECT_SOURCE_DIR}")