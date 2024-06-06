import pyModeS as pms

BITS_PER_NIBBLE = 4

# msg = "0xe83e81208a1a589b746cd52e"

# print(f"DF={pms.df(msg)} TC={pms.typecode(msg)}, ICAO={pms.icao(msg)}")
# print(pms.crc(msg, encode=False))  # Perform CRC or generate parity bit

def hex_to_binary(hex_string):
    # Convert hex string to binary string
    binary_string = bin(int(hex_string, 16))[2:]
    return binary_string

def binary_to_hex(binary_string):
    # Convert binary string to hex string
    hex_string = hex(int(binary_string, 2))[2:]
    if len(hex_string) % 2 != 0:
        hex_string = '0' + hex_string
    return hex_string

def flip_bit_at_position(binary_string, position):
    # Flip the bit at the given position
    if position < len(binary_string):
        # Convert string to list for mutation
        binary_list = list(binary_string)
        # XOR operation to flip the bit
        binary_list[position] = '1' if binary_list[position] == '0' else '0'
        # Join the list back to a string
        flipped_binary = ''.join(binary_list)
        return flipped_binary
    else:
        return "Position exceeds binary string length."

def try_bit_flips(msg_in: str):
    """
    Trys flipping each individual bit to see if it fixes a badly decoded message.
    """
    print(f"0x{msg_in}")
    if pms.crc(msg_in, encode=False) == 0:
        print(f"  OK")
        return False
    print("  INVALID")
    msg_in_bin = hex_to_binary(msg_in)
    print(f"     {msg_in_bin}")
    # Try flipping bits one by one to see if a valid decode can be retrieved.
    for i in range(len(msg_in) * BITS_PER_NIBBLE):
        try_msg_bin = flip_bit_at_position(msg_in_bin, i)
        try_msg_hex = binary_to_hex(try_msg_bin)
        decode_succeeded = pms.crc(try_msg_hex, encode=False) == 0
            
        print(f"{i:3}: {try_msg_bin} " + ("OK" if decode_succeeded else "NO"))
        if decode_succeeded: return True
    return False

if __name__ == "__main__":
    while(True):
        msg = input("Enter ADS-B message as hex string: ")
        if (msg == ""):
            msg = "0x8da1c90e|f8330002|0049b8b7|68d0"
        msg = msg.replace('|', '').replace("0x", "")
        print(msg)
        try_bit_flips(msg)