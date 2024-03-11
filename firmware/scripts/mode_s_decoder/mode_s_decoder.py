import pyModeS as pms

msg = "0xe83e81208a1a589b746cd52e"

print(f"DF={pms.df(msg)} TC={pms.typecode(msg)}, ICAO={pms.icao(msg)}")
print(pms.crc(msg, encode=False))  # Perform CRC or generate parity bit