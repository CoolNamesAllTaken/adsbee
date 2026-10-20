import base64

import pytest

from adsbee_swarm import ranges


def test_bit_i_is_byte_i_div_8_lsb_first():
    bitmap = bytearray(54)
    bitmap[0] = 0b0000_0101      # bins 0 and 2
    bitmap[53] = 0b1000_0000     # bin 431: band 11, sector 35
    values = bytes([1, 3, 255])
    decoded = ranges.decode(base64.b64encode(bitmap).decode(), base64.b64encode(values).decode(), 2000)
    assert decoded == {0: 2000, 2: 6000, 431: 510000}
    assert ranges.bin_index(11, 35) == 431


@pytest.mark.parametrize('bitmap, values, why', [
    (bytes(53), b'', '54 bytes'),
    (bytes([1]) + bytes(53), b'', 'max has 0 bytes for 1 bins'),
    (bytes([1]) + bytes(53), b'\x00', '1..255'),
])
def test_bad_maps_say_why(bitmap, values, why):
    with pytest.raises(ranges.RangeError, match=why):
        ranges.decode(base64.b64encode(bitmap).decode(), base64.b64encode(values).decode(), 2000)


def test_not_base64():
    with pytest.raises(ranges.RangeError):
        ranges.decode('!!!', '', 2000)


def test_encode_rounds_up_and_clamps_like_the_device():
    changed, maxes = ranges.encode({5: 2001, 6: 1, 7: 10_000_000}, 2000)
    assert ranges.decode(changed, maxes, 2000) == {5: 4000, 6: 2000, 7: 510000}


def test_pack_is_compact_and_round_trips():
    values = {0: 2000, 100: 40000, 431: 300000}
    blob = ranges.pack(values, 2000)
    assert len(blob) == 54 + 3
    assert ranges.unpack(blob, 2000) == values
    assert ranges.unpack(None, 2000) == {}


def test_matrix_and_sector_outline():
    values = {ranges.bin_index(0, 3): 10000, ranges.bin_index(5, 3): 90000, ranges.bin_index(11, 0): 20000}
    grid = ranges.matrix(values)
    assert len(grid) == 12 and all(len(row) == 36 for row in grid)
    assert grid[5][3] == 90000 and grid[0][0] is None
    outline = ranges.sector_max(values)
    assert outline[3] == 90000 and outline[0] == 20000 and outline[1] is None


def test_merge_is_max_per_bin():
    assert ranges.merge({1: 5, 2: 9}, {1: 7, 2: 3, 4: 1}) == {1: 7, 2: 9, 4: 1}
