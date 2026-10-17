import random

from adsbee_mlat import beast

MSG_LONG = bytes.fromhex("8D40621D58C382D690C8AC2863A7")
MSG_SHORT = bytes.fromhex("5D4840D6202CC3")


def test_round_trip_with_escapes():
    frames = [(0x1A1A1A1A1A1A, MSG_LONG), (5, MSG_SHORT), (0xFFFFFFFFFFFF, b"\x1a" * 14)]
    data = b"".join(beast.build_mode_s(t, m, signal=0x1A) for t, m in frames)
    out, infos, ids = beast.BeastParser().feed(data)
    assert [(t, m) for t, _, m in out] == frames
    assert all(s == 0x1A for _, s, _ in out)
    assert not infos and not ids


def test_split_at_every_byte():
    info = beast.build_info(id="0bee00038172d18c", ep="3fa2", clk=48_000_000, lat=37.4219983, lon=-122.0840575,
                            alt=31.42, src="gnss", hacc=2.5, pps="2f1c0a39b100@1791936000")
    data = info + b"".join(beast.build_mode_s(0x1A00001A0000 + k, MSG_LONG) for k in range(20))
    for cut in range(1, len(data)):
        p = beast.BeastParser()
        a = p.feed(data[:cut])
        b = p.feed(data[cut:])
        frames = a[0] + b[0]
        infos = a[1] + b[1]
        assert len(frames) == 20, cut
        assert len(infos) == 1
    i = infos[0]
    assert i["id"] == "0bee00038172d18c" and i["clk"] == 48_000_000 and i["ep"] == "3fa2"
    assert abs(i["lat"] - 37.4219983) < 1e-9 and i["src"] == "gnss" and i["pps"] == (0x2F1C0A39B100, 1791936000)


def test_info_frame_has_no_escape_byte():
    info = beast.build_info(id="x", ep="1a", clk=12_000_000, lat=26.0, lon=26.0, alt=26.0, src="fixed")
    assert info.count(b"\x1a") == 1  # Only the frame start: legacy parsers skip to the next frame.


def test_resync_after_garbage_and_unknown_types():
    rnd = random.Random(1)
    good = [beast.build_mode_s(k, MSG_LONG) for k in range(50)]
    data = b""
    for g in good:
        data += bytes(rnd.choice([0x00, 0x55, 0x31]) for _ in range(rnd.randint(0, 5)))
        data += b"\x1a\xec" + b"lfoo"  # UAT frame we skip.
        data += g
    out, _, _ = beast.BeastParser().feed(data)
    assert [t for t, _, _ in out] == list(range(50))


def test_truncated_frame_is_dropped():
    a = beast.build_mode_s(1, MSG_LONG)[:-4]
    b = beast.build_mode_s(2, MSG_LONG)
    out, _, _ = beast.BeastParser().feed(a + b)
    assert [t for t, _, _ in out] == [2]


def test_feed_id_frame():
    uuid = b"38366a5c-c54f-4256-bd0a-1557961f5ad0"
    out, _, ids = beast.BeastParser().feed(b"\x1a\xe4" + uuid + beast.build_mode_s(7, MSG_SHORT))
    assert ids == [uuid.decode()] and out[0][0] == 7


def test_bad_info_ignored():
    p = beast.BeastParser()
    out, infos, _ = p.feed(b"\x1a\xe9no_equals_sign\n" + beast.build_mode_s(3, MSG_SHORT))
    assert infos == [] and out[0][0] == 3 and p.bad_frames == 1


def test_short_info_frame_starts_each_udp_datagram():
    # What ADSBee firmware sends between full info frames on UDP: v, id, clk and ep, then whole frames.
    short = b"\x1a\xe9v=1;id=bee00038172d18c1;clk=48000000;ep=5a3c91e2\n"
    datagram = short + b"".join(beast.build_mode_s(1000 + k, MSG_LONG) for k in range(50))
    frames, infos, _ = beast.BeastParser().feed(datagram)
    assert len(frames) == 50
    assert infos == [{"v": 1, "id": "bee00038172d18c1", "clk": 48_000_000, "ep": "5a3c91e2"}]

    # A server that hears of the receiver from a short frame first gets its clock rate right.
    from adsbee_mlat.engine import Engine
    rx = Engine().apply_info(infos[0])
    assert rx.clock_hz == 48_000_000
