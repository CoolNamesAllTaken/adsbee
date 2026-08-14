// BLE GATT transport for GDL90 - see comms_ble.hh for the service layout and design rationale.
//
// Shares the NimBLE host with Broadcast Remote ID (remote_id_ble.cpp): Remote ID owns the non-connectable advertising
// instances 0 (BT4 legacy ODID) and 1 (BT5 Long Range pack); this module owns the connectable instance 2 that carries
// the ADS-B Receiver Service UUID and device name. Whichever feature starts first brings the host up via
// BleHostEnsureInitialized(), which also registers this module's GATT services at the only point where NimBLE allows
// it (before the host task runs).

#include "comms_ble.hh"

#include "sdkconfig.h"

#if defined(CONFIG_BT_ENABLED) && defined(CONFIG_BT_NIMBLE_ENABLED) && defined(CONFIG_BT_NIMBLE_ROLE_PERIPHERAL)

#include <cstring>

#include "ble_host.hh"  // BleHostEnsureInitialized (shared with Remote ID).
#include "comms.hh"     // Logging.
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "host/ble_att.h"  // ble_att_mtu.
#include "host/ble_gap.h"
#include "host/ble_hs.h"
#include "host/util/util.h"
#include "os/os_mbuf.h"
#include "services/gap/ble_svc_gap.h"
#include "services/gatt/ble_svc_gatt.h"

namespace ble_gdl90 {
namespace {

constexpr uint8_t kAdvInstance = 2;  // Instances 0/1 belong to Remote ID (remote_id_ble.cpp).
constexpr uint32_t kAdvIntervalMs = 200;
constexpr uint32_t kAdvIntervalUnits = (kAdvIntervalMs * 1000) / 625;  // NimBLE units of 0.625 ms.
constexpr char kDeviceName[] = "ADSBee";
// Notify payload must fit in ATT_MTU-3; GDL90 traffic reports are ~30 framed bytes, well within even the default MTU
// after the preferred-MTU exchange (CONFIG_BT_NIMBLE_ATT_PREFERRED_MTU=256).
constexpr uint16_t kMaxNotifyPayloadBytes = 244;

// UUID base 0BEExxxx-1090-46F0-A9AC-52D6BE4C29CC, bytes in NimBLE little-endian order.
#define BLE_GDL90_UUID128(idx_lo, idx_hi)                                                                            \
    BLE_UUID128_INIT(0xCC, 0x29, 0x4C, 0xBE, 0xD6, 0x52, 0xAC, 0xA9, 0xF0, 0x46, 0x90, 0x10, idx_lo, idx_hi, 0xEE, \
                     0x0B)

const ble_uuid128_t kServiceUUID = BLE_GDL90_UUID128(0x01, 0x00);
const ble_uuid128_t kTrafficUUID = BLE_GDL90_UUID128(0x10, 0x00);
const ble_uuid128_t kOwnshipUUID = BLE_GDL90_UUID128(0x11, 0x00);
const ble_uuid128_t kStatusUUID = BLE_GDL90_UUID128(0x12, 0x00);
const ble_uuid128_t kUplinkUUID = BLE_GDL90_UUID128(0x13, 0x00);
const ble_uuid128_t kControlUUID = BLE_GDL90_UUID128(0x20, 0x00);

uint16_t g_traffic_val_handle = 0;
uint16_t g_ownship_val_handle = 0;
uint16_t g_status_val_handle = 0;
uint16_t g_uplink_val_handle = 0;

// Uplink fragmentation (see comms_ble.hh): header bit7 first, bit6 last, bits 0-5 sequence mod 64.
constexpr uint8_t kUplinkFragmentFirst = 0x80;
constexpr uint8_t kUplinkFragmentLast = 0x40;
constexpr uint16_t kUplinkMinMTUBytes = 100;  // Skip uplink on default-MTU links; FIS-B would drown them.
uint8_t g_uplink_sequence = 0;

bool g_services_registered = false;
bool g_advertising_configured = false;
bool g_started = false;
bool g_advertising = false;

// Diagnostics: early boot logs are lost before the RP2040 SPI console bridge comes up, so remember the last result
// codes and report them periodically from a status task.
int g_last_configure_rc = -1;
int g_last_set_data_rc = -1;
int g_last_adv_start_rc = -1;
int g_host_init_err = -1;

// Per-connection subscription state, indexed by characteristic.
struct ClientConnection {
    uint16_t conn_handle = BLE_HS_CONN_HANDLE_NONE;
    bool traffic_subscribed = false;
    bool ownship_subscribed = false;
    bool status_subscribed = false;
    bool uplink_subscribed = false;

    bool InUse() const { return conn_handle != BLE_HS_CONN_HANDLE_NONE; }
    void Clear() { *this = ClientConnection(); }
};
ClientConnection g_connections[CONFIG_BT_NIMBLE_MAX_CONNECTIONS];

ClientConnection* FindConnection(uint16_t conn_handle) {
    for (auto& conn : g_connections) {
        if (conn.InUse() && conn.conn_handle == conn_handle) return &conn;
    }
    return nullptr;
}

int GattAccessCallback(uint16_t conn_handle, uint16_t attr_handle, struct ble_gatt_access_ctxt* ctxt, void* arg) {
    switch (ctxt->op) {
        case BLE_GATT_ACCESS_OP_WRITE_CHR: {
            // Control characteristic: reserved for configuration commands; accept and log for now.
            uint16_t len = OS_MBUF_PKTLEN(ctxt->om);
            CONSOLE_INFO("ble_gdl90", "Control write received (%u bytes).", len);
            return 0;
        }
        default:
            // Notify-only characteristics have no read access.
            return BLE_ATT_ERR_READ_NOT_PERMITTED;
    }
}

const struct ble_gatt_chr_def kCharacteristics[] = {
    {
        .uuid = &kTrafficUUID.u,
        .access_cb = GattAccessCallback,
        .flags = BLE_GATT_CHR_F_NOTIFY,
        .val_handle = &g_traffic_val_handle,
    },
    {
        .uuid = &kOwnshipUUID.u,
        .access_cb = GattAccessCallback,
        .flags = BLE_GATT_CHR_F_NOTIFY,
        .val_handle = &g_ownship_val_handle,
    },
    {
        .uuid = &kStatusUUID.u,
        .access_cb = GattAccessCallback,
        .flags = BLE_GATT_CHR_F_NOTIFY,
        .val_handle = &g_status_val_handle,
    },
    {
        .uuid = &kUplinkUUID.u,
        .access_cb = GattAccessCallback,
        .flags = BLE_GATT_CHR_F_NOTIFY,
        .val_handle = &g_uplink_val_handle,
    },
    {
        .uuid = &kControlUUID.u,
        .access_cb = GattAccessCallback,
        .flags = BLE_GATT_CHR_F_WRITE | BLE_GATT_CHR_F_WRITE_NO_RSP,
    },
    {0},  // Terminator.
};

const struct ble_gatt_svc_def kServices[] = {
    {
        .type = BLE_GATT_SVC_TYPE_PRIMARY,
        .uuid = &kServiceUUID.u,
        .characteristics = kCharacteristics,
    },
    {0},  // Terminator.
};

int GapEventHandler(struct ble_gap_event* event, void* arg);

// Configures and starts the connectable advertising instance carrying the service UUID and name. The instance stops
// whenever a central connects; call again to keep accepting additional clients.
void StartAdvertising() {
    // Make sure the controller has a usable address before advertising (same prerequisite as the NimBLE examples).
    int addr_rc = ble_hs_util_ensure_addr(0);
    if (addr_rc != 0) {
        g_last_configure_rc = addr_rc;
        return;
    }
    if (!g_advertising_configured) {
        struct ble_gap_ext_adv_params params;
        memset(&params, 0, sizeof(params));
        params.connectable = 1;
        params.scannable = 1;  // Legacy connectable advertisements must be scannable (ADV_IND).
        params.legacy_pdu = 1;
        params.itvl_min = kAdvIntervalUnits;
        params.itvl_max = kAdvIntervalUnits;
        params.own_addr_type = BLE_OWN_ADDR_PUBLIC;
        params.primary_phy = BLE_HCI_LE_PHY_1M;
        params.secondary_phy = BLE_HCI_LE_PHY_1M;
        params.sid = kAdvInstance;
        params.tx_power = 127;  // Let the controller pick its maximum.

        int8_t selected_tx_power = 0;
        int rc = ble_gap_ext_adv_configure(kAdvInstance, &params, &selected_tx_power, GapEventHandler, nullptr);
        g_last_configure_rc = rc;
        if (rc != 0) {
            CONSOLE_ERROR("ble_gdl90", "ble_gap_ext_adv_configure(%u) failed, rc=%d.", kAdvInstance, rc);
            return;
        }

        // AD payload: flags + 128-bit service UUID + shortened name. 3 + 18 + 2 + name <= 31 bytes.
        uint8_t ad[BLE_HS_ADV_MAX_SZ];
        uint8_t i = 0;
        ad[i++] = 2;  // Flags.
        ad[i++] = BLE_HS_ADV_TYPE_FLAGS;
        ad[i++] = BLE_HS_ADV_F_DISC_GEN | BLE_HS_ADV_F_BREDR_UNSUP;
        ad[i++] = 17;  // Complete list of 128-bit service UUIDs.
        ad[i++] = BLE_HS_ADV_TYPE_COMP_UUIDS128;
        memcpy(&ad[i], kServiceUUID.value, 16);
        i += 16;
        uint8_t name_len = strlen(kDeviceName);
        ad[i++] = name_len + 1;
        ad[i++] = BLE_HS_ADV_TYPE_COMP_NAME;
        memcpy(&ad[i], kDeviceName, name_len);
        i += name_len;

        struct os_mbuf* om = os_msys_get_pkthdr(i, 0);
        if (om == nullptr || os_mbuf_append(om, ad, i) != 0) {
            if (om != nullptr) os_mbuf_free_chain(om);
            CONSOLE_ERROR("ble_gdl90", "Failed to allocate advertising data mbuf.");
            return;
        }
        rc = ble_gap_ext_adv_set_data(kAdvInstance, om);  // Consumes the mbuf.
        g_last_set_data_rc = rc;
        if (rc != 0) {
            CONSOLE_ERROR("ble_gdl90", "ble_gap_ext_adv_set_data failed, rc=%d.", rc);
            return;
        }
        g_advertising_configured = true;
    }

    int rc = ble_gap_ext_adv_start(kAdvInstance, /*duration=*/0, /*max_events=*/0);
    g_last_adv_start_rc = rc;
    g_advertising = (rc == 0 || rc == BLE_HS_EALREADY);
    if (rc != 0 && rc != BLE_HS_EALREADY) {
        CONSOLE_ERROR("ble_gdl90", "ble_gap_ext_adv_start failed, rc=%d.", rc);
    }
}

// Periodic status heartbeat so the state is observable once the RP2040 console bridge is up (one-shot boot-time logs
// are lost before the SPI link exists, and the default console level filters INFO). Also self-heals: boot-time
// advertising failures (host not yet synced, controller address not ready) are retried here.
void StatusTask(void* param) {
    while (true) {
        vTaskDelay(pdMS_TO_TICKS(30'000));
        if (g_started && ble_hs_synced() && !g_advertising) {
            StartAdvertising();  // Retry: boot-time attempt may have preceded host sync.
        }
        uint16_t num_connected = 0;
        for (auto& conn : g_connections) {
            if (conn.InUse()) num_connected++;
        }
        CONSOLE_WARNING("ble_gdl90",
                        "started=%d host_init_err=%d synced=%d svcs=%d adv_cfg=%d adv=%d rc_cfg=%d rc_data=%d "
                        "rc_start=%d conns=%u subs=%d",
                        (int)g_started, g_host_init_err, (int)ble_hs_synced(), (int)g_services_registered,
                        (int)g_advertising_configured, (int)g_advertising, g_last_configure_rc, g_last_set_data_rc,
                        g_last_adv_start_rc, num_connected, (int)HasSubscribers());
    }
}

uint16_t NumFreeConnections() {
    uint16_t free_count = 0;
    for (auto& conn : g_connections) {
        if (!conn.InUse()) free_count++;
    }
    return free_count;
}

int GapEventHandler(struct ble_gap_event* event, void* arg) {
    switch (event->type) {
        case BLE_GAP_EVENT_CONNECT: {
            if (event->connect.status == 0) {
                for (auto& conn : g_connections) {
                    if (!conn.InUse()) {
                        conn.Clear();
                        conn.conn_handle = event->connect.conn_handle;
                        break;
                    }
                }
                CONSOLE_INFO("ble_gdl90", "Client connected (handle %u).", event->connect.conn_handle);
            }
            // Advertising stops on connect; resume if there is room for more clients.
            if (NumFreeConnections() > 0) StartAdvertising();
            return 0;
        }
        case BLE_GAP_EVENT_DISCONNECT: {
            ClientConnection* conn = FindConnection(event->disconnect.conn.conn_handle);
            if (conn != nullptr) conn->Clear();
            CONSOLE_INFO("ble_gdl90", "Client disconnected (reason %d).", event->disconnect.reason);
            StartAdvertising();
            return 0;
        }
        case BLE_GAP_EVENT_SUBSCRIBE: {
            ClientConnection* conn = FindConnection(event->subscribe.conn_handle);
            if (conn == nullptr) return 0;
            if (event->subscribe.attr_handle == g_traffic_val_handle) {
                conn->traffic_subscribed = event->subscribe.cur_notify;
            } else if (event->subscribe.attr_handle == g_ownship_val_handle) {
                conn->ownship_subscribed = event->subscribe.cur_notify;
            } else if (event->subscribe.attr_handle == g_status_val_handle) {
                conn->status_subscribed = event->subscribe.cur_notify;
            } else if (event->subscribe.attr_handle == g_uplink_val_handle) {
                conn->uplink_subscribed = event->subscribe.cur_notify;
            }
            return 0;
        }
        default:
            return 0;
    }
}

// Selects the subscription flag matching a GDL90 message ID, or nullptr for messages not carried over BLE.
bool ClientConnection::* SubscriptionForMessageID(uint8_t message_id) {
    switch (message_id) {
        case 0x14:  // Traffic Report.
        case 30:    // UAT Basic Report.
        case 31:    // UAT Long Report.
            return &ClientConnection::traffic_subscribed;
        case 0x0A:  // Ownship Report.
        case 0x0B:  // Ownship Geometric Altitude.
            return &ClientConnection::ownship_subscribed;
        case 0x00:  // Heartbeat.
        case 0x02:  // Initialization.
            return &ClientConnection::status_subscribed;
        default:
            return nullptr;  // UAT uplink (0x07) etc: too large for a notification, WiFi only.
    }
}

uint16_t ValHandleForMessageID(uint8_t message_id) {
    bool ClientConnection::* subscription = SubscriptionForMessageID(message_id);
    if (subscription == &ClientConnection::traffic_subscribed) return g_traffic_val_handle;
    if (subscription == &ClientConnection::ownship_subscribed) return g_ownship_val_handle;
    if (subscription == &ClientConnection::status_subscribed) return g_status_val_handle;
    return 0;
}

}  // namespace

bool RegisterServices() {
    if (g_services_registered) return true;
    ble_svc_gap_init();
    ble_svc_gatt_init();
    int rc = ble_gatts_count_cfg(kServices);
    if (rc != 0) {
        CONSOLE_ERROR("ble_gdl90", "ble_gatts_count_cfg failed, rc=%d.", rc);
        return false;
    }
    rc = ble_gatts_add_svcs(kServices);
    if (rc != 0) {
        CONSOLE_ERROR("ble_gdl90", "ble_gatts_add_svcs failed, rc=%d.", rc);
        return false;
    }
    ble_svc_gap_device_name_set(kDeviceName);
    g_services_registered = true;
    return true;
}

void OnHostSync() {
    if (!g_started) return;
    StartAdvertising();
}

bool Start() {
    if (g_started) return true;
    xTaskCreate(StatusTask, "ble_gdl90_status", 4096, nullptr, 1, nullptr);
    bool host_ok = BleHostEnsureInitialized();
    g_host_init_err = host_ok ? 0 : 1;
    if (!host_ok) return false;
    g_started = true;
    // If the host already synced (Remote ID brought it up first), start advertising now; otherwise the shared sync
    // callback will call OnHostSync().
    if (ble_hs_synced()) StartAdvertising();
    CONSOLE_INFO("ble_gdl90", "BLE ADS-B Receiver Service started.");
    return true;
}

bool HasSubscribers() {
    for (auto& conn : g_connections) {
        if (conn.InUse() && (conn.traffic_subscribed || conn.ownship_subscribed || conn.status_subscribed ||
                             conn.uplink_subscribed)) {
            return true;
        }
    }
    return false;
}

// Fragments one framed uplink message onto the Uplink characteristic for every subscribed client whose link MTU can
// sustain FIS-B. Fragment payload is sized to the connection's negotiated MTU so a 517-byte MTU link usually gets the
// whole message in one notification.
bool SendUplink(const uint8_t* buf, uint16_t len_bytes) {
    bool sent = false;
    for (auto& conn : g_connections) {
        if (!conn.InUse() || !conn.uplink_subscribed) continue;
        uint16_t mtu = ble_att_mtu(conn.conn_handle);
        if (mtu < kUplinkMinMTUBytes) continue;
        uint16_t max_fragment_bytes = mtu - 3 /*ATT notify overhead*/ - 1 /*fragment header*/;

        uint16_t offset = 0;
        bool ok = true;
        while (offset < len_bytes) {
            uint16_t fragment_bytes =
                (len_bytes - offset) < max_fragment_bytes ? (len_bytes - offset) : max_fragment_bytes;
            uint8_t header = g_uplink_sequence & 0x3F;
            if (offset == 0) header |= kUplinkFragmentFirst;
            if (offset + fragment_bytes >= len_bytes) header |= kUplinkFragmentLast;
            g_uplink_sequence = (g_uplink_sequence + 1) & 0x3F;

            struct os_mbuf* om = os_msys_get_pkthdr(1 + fragment_bytes, 0);
            if (om == nullptr || os_mbuf_append(om, &header, 1) != 0 ||
                os_mbuf_append(om, buf + offset, fragment_bytes) != 0) {
                if (om != nullptr) os_mbuf_free_chain(om);
                ok = false;
                break;  // Out of mbufs; the client's reassembler discards the partial on the next first fragment.
            }
            if (ble_gatts_notify_custom(conn.conn_handle, g_uplink_val_handle, om) != 0) {
                ok = false;
                break;
            }
            offset += fragment_bytes;
        }
        sent = sent || ok;
    }
    return sent;
}

bool SendGDL90Message(const uint8_t* buf, uint16_t len_bytes) {
    if (len_bytes < 2) return false;
    uint8_t message_id = buf[1];  // Framed message: [0x7E][ID][payload...][CRC][0x7E].
    if (message_id == 0x07) {
        return SendUplink(buf, len_bytes);  // FIS-B uplink: fragmented onto its own characteristic.
    }
    if (len_bytes > kMaxNotifyPayloadBytes) return false;
    bool ClientConnection::* subscription = SubscriptionForMessageID(message_id);
    if (subscription == nullptr) return false;
    uint16_t val_handle = ValHandleForMessageID(message_id);

    bool sent = false;
    for (auto& conn : g_connections) {
        if (!conn.InUse() || !(conn.*subscription)) continue;
        struct os_mbuf* om = ble_hs_mbuf_from_flat(buf, len_bytes);
        if (om == nullptr) return sent;  // Out of mbufs; drop, the next report replaces it.
        int rc = ble_gatts_notify_custom(conn.conn_handle, val_handle, om);
        if (rc == 0) {
            sent = true;
        }
    }
    return sent;
}

}  // namespace ble_gdl90

#else  // Bluetooth peripheral role not compiled in: no-op stubs.

namespace ble_gdl90 {
bool RegisterServices() { return false; }
void OnHostSync() {}
bool Start() { return false; }
bool SendGDL90Message(const uint8_t*, uint16_t) { return false; }
bool HasSubscribers() { return false; }
}  // namespace ble_gdl90

#endif  // CONFIG_BT_ENABLED && CONFIG_BT_NIMBLE_ENABLED && CONFIG_BT_NIMBLE_ROLE_PERIPHERAL
