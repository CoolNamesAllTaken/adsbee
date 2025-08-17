// Auto-generated UAT test data header for Google Test
// Self-contained - no external dependencies required
#ifndef UAT_TEST_DATA_H
#define UAT_TEST_DATA_H

#include <stdint.h>

// Enum value constants
#define UAT_ALT_INVALID 0
#define UAT_ALT_BARO    1
#define UAT_ALT_GEO     2

#define UAT_TT_INVALID      0
#define UAT_TT_TRACK        1
#define UAT_TT_MAG_HEADING  2
#define UAT_TT_TRUE_HEADING 3

#define UAT_CS_INVALID   0
#define UAT_CS_CALLSIGN  1
#define UAT_CS_SQUAWK    2

#define UAT_HT_TRUE      0
#define UAT_HT_MAGNETIC  1

// Downlink test frame structure
typedef struct {
    const char* frame_data_hex;
    int frame_length;
    const char* test_name;
    
    // Decoded HDR fields
    int mdb_type;
    int address_qualifier;
    uint32_t address;
    
    // Decoded SV fields
    int has_sv;
    int nic;
    int position_valid;
    double lat;
    double lon;
    int altitude_type;
    int altitude;
    int airground_state;
    int ns_vel_valid;
    int ns_vel;
    int ew_vel_valid;
    int ew_vel;
    int track_type;
    uint16_t track;
    int speed_valid;
    uint16_t speed;
    int vert_rate_source;
    int vert_rate;
    int dimensions_valid;
    double length;
    double width;
    int position_offset;
    int utc_coupled;
    int tisb_site_id;
    
    // Decoded MS fields
    int has_ms;
    int emitter_category;
    char callsign[9];
    int callsign_type;
    int emergency_status;
    int uat_version;
    int sil;
    int transmit_mso;
    int nac_p;
    int nac_v;
    int nic_baro;
    int has_cdti;
    int has_acas;
    int acas_ra_active;
    int ident_active;
    int atc_services;
    int heading_type;
    
    // Decoded AUXSV fields
    int has_auxsv;
    int sec_altitude_type;
    int sec_altitude;
} uat_downlink_test_frame_t;

// Uplink test frame structure
typedef struct {
    const char* frame_data_hex;
    int frame_length;
    const char* test_name;
    
    // Decoded uplink fields
    int position_valid;
    double lat;
    double lon;
    int utc_coupled;
    int app_data_valid;
    int slot_id;
    int tisb_site_id;
    int num_info_frames;
    
    // Info frame data
    struct {
        int length;
        int type;
        int is_fisb;
        int fisb_product_id;
        int fisb_a_flag;
        int fisb_g_flag;
        int fisb_p_flag;
        int fisb_s_flag;
        int fisb_hours;
        int fisb_minutes;
        int fisb_seconds;
        int fisb_seconds_valid;
        int fisb_month;
        int fisb_day;
        int fisb_monthday_valid;
    } info_frames[8];
} uat_uplink_test_frame_t;

#ifdef __cplusplus
extern "C" {
#endif

// Function declarations
const uat_downlink_test_frame_t* get_uat_downlink_test_frames();
int get_uat_downlink_test_frames_count();
const uat_downlink_test_frame_t* get_uat_downlink_test_frame(int index);

const uat_uplink_test_frame_t* get_uat_uplink_test_frames();
int get_uat_uplink_test_frames_count();
const uat_uplink_test_frame_t* get_uat_uplink_test_frame(int index);

#ifdef __cplusplus
}
#endif

#endif // UAT_TEST_DATA_H
