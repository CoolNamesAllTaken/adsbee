#include "comms.hh"

bool CommsManager::Init() {
    InitAT();
    return true;
}

bool CommsManager::Update() {
    UpdateAT();
    return true;
}