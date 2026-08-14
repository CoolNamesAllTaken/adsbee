#pragma once

// Shared NimBLE host bring-up, owned by remote_id_ble.cpp and used by every BLE feature (Broadcast Remote ID
// scan/transmit, the GDL90 GATT service in comms/comms_ble.cpp). The host and controller are initialized exactly once;
// GATT services are registered during that bring-up, which is the only point where NimBLE allows it. Returns false if
// Bluetooth is not in the build or the stack failed to initialize.
bool BleHostEnsureInitialized();
