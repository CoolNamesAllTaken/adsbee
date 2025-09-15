#include "composite_array.hh"

CompositeArray::RawPackets CompositeArray::FillRawPacketsBuffer(uint8_t* buf, uint16_t buf_len,
                                                                PFBQueue<RawModeSPacket>& mode_s_queue,
                                                                PFBQueue<RawUATADSBPacket>& uat_adsb_queue,
                                                                PFBQueue<RawUATUplinkPacket>& uat_uplink_queue) {}