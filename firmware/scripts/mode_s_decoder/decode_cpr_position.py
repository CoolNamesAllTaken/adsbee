import pyModeS as pms

def decode_cpr_pos_from_packet_pair(packet_a, packet_b):
    """
    Decode a lat/lon position from a pair of Compact Position Reporting (CPR) packets.
    Args:
        packet_a = Raw hex string of first CPR packet.
        packet_b = Raw hex string of complementary CPR packet.
    Returns:
        Tuple of floats in the form (lat_deg, lon_deg).
    """
    pos = pms.adsb.airborne_position(packet_a, packet_b, 0, 0)
    return pos

if __name__ == "__main__":
    while(True):
        packet_a = input("CPR Packet A: ")
        packet_b = input("CPR packet B: ")
        print(decode_cpr_pos_from_packet_pair(packet_a, packet_b))
