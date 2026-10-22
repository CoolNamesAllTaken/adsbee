import json
import os
import threading
import time

import pytest

from adsbee_hil import remote_id as rid
from adsbee_hil.config import Bench, ReceiverConfig
from adsbee_hil.receivers import Adsbee1090U

TX_Q = ("REMOTE_ID_TX=1,BT4+BT5_LR(TRANSPORTS),(device serial)(UAS_ID),1(ID_TYPE),2(UA_TYPE),(none)(OPERATOR_ID),"
        "BT_SCANNING+BT5_LR_SCANNING+TX_BT4+TX_BT5_LR+TX_NO_POSITION+TX_POSITION_SOURCE_NOT_ALLOWED(ESP32_STATUS),"
        "BT4+BT5_LR(ALLOWED_TRANSPORTS)")
RX_Q = "REMOTE_ID=1,BT4+BT5_LR(TRANSPORTS),BT_SCANNING+BT5_LR_SCANNING(ESP32_STATUS),BT4+BT5_LR(ALLOWED_TRANSPORTS)"


def test_parse_rid_query():
    f = rid.parse_rid_query("junk\r\n" + TX_Q + "\r\nOK", "REMOTE_ID_TX")
    assert f["ENABLED"] == "1" and f["TRANSPORTS"] == "BT4+BT5_LR" and f["UAS_ID"] == "(device serial)"
    assert f["OPERATOR_ID"] == "(none)" and f["ALLOWED_TRANSPORTS"] == "BT4+BT5_LR"
    assert "TX_NO_POSITION" in rid.status_words(f)
    assert rid.parse_rid_query(TX_Q, "REMOTE_ID") is None  # REMOTE_ID= must not match REMOTE_ID_TX=.
    old = rid.parse_rid_query("REMOTE_ID=0,0x03(TRANSPORTS),0x00(ESP32_STATUS)", "REMOTE_ID")
    assert rid.transports_arg(old["TRANSPORTS"]) == "BT4+BT5_LR"
    assert rid.status_words({"ESP32_STATUS": "NONE"}) == []


def test_expected_status():
    assert rid.expected_status(rid.Role(tx="BT4")) == ["TX_BT4", "TX_NO_POSITION"]
    assert rid.expected_status(rid.Role(rx="BT4")) == ["BT_SCANNING"]
    assert rid.expected_status(rid.Role(rx=rid.BLE, tx=rid.BLE)) == [
        "BT_SCANNING", "BT5_LR_SCANNING", "TX_BT4", "TX_BT5_LR", "TX_NO_POSITION"]


def test_unit_spec():
    s = rid.UnitSpec.parse("adsbee-ci@10.0.0.2:bench")
    assert (s.ssh, s.device) == ("adsbee-ci@10.0.0.2", "bench")
    assert rid.UnitSpec.parse("E123").ssh is None
    cmd = rid.unit_command(s, rid.Role(rx=rid.BLE), "X", "Y", 100.0, 5, 60, False, None, "~/v/bin/adsbee-hil",
                           "~/b.toml", 30)
    assert cmd[:2] == ["ssh", "-o"] and "remote-id-unit bench" in cmd[-1] and "--peer-uas-id Y" in cmd[-1]
    assert cmd[-1].startswith("~/v/bin/adsbee-hil -c ~/b.toml --lock-timeout 30 remote-id-unit")


def _win(i, **kw):
    r = {"ev": "window", "i": i, "wd_scan": 0, "wd_adv": 0, "host_resets": 0, "ble_errors": 0, "heap_pauses": 0,
         "spi_errors": 0, "esp32_reboots": 0, "heartbeat_gaps_s": []}
    r.update(kw)
    return r


def _unit(name, windows, **end):
    status = {"ev": "status", "applied_s": 2.0, "want": [], "rx_status": [], "tx_status": []}
    return [{"ev": "start", "unit": name, "found": {"versions": {"RP2040": "0.9.1-rc9"}}}, status] + windows + [
        {"ev": "end", "errors": [], "restore_failed": [], "config_hash_restored": True, **end}]


def test_judge_pass_and_empty_minute():
    a = _unit("a", [_win(i, heap_min_kb=90, heap_med_kb=94) for i in range(3)])
    b = _unit("b", [_win(i, rid_frames=100, metrics_s=60, rid_per_s=1.7) for i in range(3)])
    verdict, lines = rid.judge("tx-both", {"A": a, "B": b}, 3, 60)
    assert verdict == "PASS", lines
    assert "RX 1.67 frames/s, empty windows 0/3" in lines[1]
    b[3]["rid_frames"] = 0
    verdict, lines = rid.judge("tx-both", {"A": a, "B": b}, 3, 60)
    assert verdict == "FAIL" and "1 window(s) without Remote ID" in lines[-1]


def test_judge_reboot_and_restore_fail():
    a = _unit("a", [_win(0, esp32_reboots=1)], config_hash_restored=False)
    b = _unit("b", [_win(0)])
    verdict, lines = rid.judge("off", {"A": a, "B": b}, 1, 60)
    assert verdict == "FAIL" and "ESP32" in lines[-1] and "not restored" in lines[-1]


class FakeRidUnit:
    """A pty that answers the AT commands run_unit sends and streams ESP32 heartbeats and aircraft JSON."""

    def __init__(self, fake_at, peer="ADSBEEBENCHA"):
        self.state = {"rx": "0", "tx": "0", "log": "WARNINGS", "proto": "MAVLINK1"}
        replies = {}
        self.dev = fake_at(replies)
        self.replies = replies
        self.peer = peer
        self._refresh()
        self._stop = False
        threading.Thread(target=self._stream, daemon=True).start()

    def _refresh(self):
        st = self.state
        rx_words = "BT_SCANNING+BT5_LR_SCANNING" if st["rx"] == "1" else "NONE"
        self.replies.clear()
        self.replies.update({
            "AT+UPTIME?": "+UPTIME=100",
            "AT+DEVICE_INFO?": "RP2040 Firmware Version: 0.9.1-rc9\r\nESP32 Firmware Version: 0.9.1-rc9\r\n"
                               "ESP32 PSRAM: NONE\r\nOTA Key 0: hush",
            "AT+REMOTE_ID?": f"REMOTE_ID={st['rx']},BT4+BT5_LR(TRANSPORTS),{rx_words}(ESP32_STATUS),"
                             "BT4+BT5_LR(ALLOWED_TRANSPORTS)",
            "AT+REMOTE_ID_TX?": f"REMOTE_ID_TX={st['tx']},BT4(TRANSPORTS),(device serial)(UAS_ID),1(ID_TYPE),"
                                f"2(UA_TYPE),(none)(OPERATOR_ID),{rx_words}(ESP32_STATUS),"
                                "BT4+BT5_LR(ALLOWED_TRANSPORTS)",
            "AT+LOG_LEVEL?": f"LOG_LEVEL={st['log']}",
            "AT+PROTOCOL_OUT?": f"PROTOCOL_OUT=CONSOLE,{st['proto']}\r\nPROTOCOL_OUT=COMMS_UART,NONE",
            "AT+RX_POSITION?": "Receiver Position:\r\n\tSource: LOWEST [NOT AVAILABLE]",
            "AT+FEED_ENABLE?": "FEED_ENABLE=1",
            "AT+ESP32_REBOOT_INFO?": "ESP32 Reset Reason: 1 (POWERON)",
            "AT+CONFIG_HASH?": f"SETTINGS_FULL=0x{hash(tuple(st.items())) & 0xFFFFFFFF:08X}",
            "AT+WIFI_AP?": "WIFI_AP=0,ssid,secretpass,1",
            "AT+ETHERNET?": "ETHERNET=1",
            "AT+WIFI_STA?": "WIFI_STA=0,net,pw",
        })
        for v in ("INFO", "WARNINGS"):
            self.replies[f"AT+LOG_LEVEL={v}"] = self._setter("log", v)
        for v in ("AIRCRAFT_JSON", "MAVLINK1"):
            self.replies[f"AT+PROTOCOL_OUT=CONSOLE,{v}"] = self._setter("proto", v)
        for t in ("BT4+BT5_LR", "BT4"):
            self.replies[f"AT+REMOTE_ID=1,{t}"] = self._setter("rx", "1")
        self.replies["AT+REMOTE_ID=0"] = self._setter("rx", "0")
        self.replies["AT+REMOTE_ID=0,BT4+BT5_LR"] = self._setter("rx", "0")
        self.replies["AT+REMOTE_ID_TX=0"] = ""
        self.replies["AT+REMOTE_ID_TX=0,BT4,-,1,2,-"] = ""

    def _setter(self, key, value):
        unit = self

        class Reply(str):
            def __new__(cls):
                return str.__new__(cls, "")

            def __add__(self, other):  # FakeAtDevice builds the reply as reply + "\r\nOK\r\n".
                unit.state[key] = value
                unit._refresh()
                return str(self) + other
        return Reply()

    def _stream(self):
        while not self._stop:
            lines = ["CoProcessor: ESP32 >> [ADSBeeServer::Update] \t 0 clients, 3 aircraft, heap: 64K free / 229K "
                     "total, ws: 0/16"]
            if self.state["proto"] == "AIRCRAFT_JSON":
                rssi = -50 - int(time.time() * 10) % 7
                lines.append(json.dumps({"hex": "~12abcd", "type": "remote_id", "flight": self.peer,
                                         "rssi": rssi, "rid_uas_id": self.peer}, separators=(",", ":")))
            try:
                os.write(self.dev.master, ("\r\n".join(lines) + "\r\n").encode())
            except OSError:
                return
            time.sleep(0.2)

    def close(self):
        self._stop = True


@pytest.fixture
def fake_unit(fake_at, fake_sysfs):
    u = FakeRidUnit(fake_at)
    fake_sysfs.add("1-1.3", "2e8a", "000a", "P1090", "Pants for Birds", "ADSBee 1090", "ttyACM0",
                   "usb-Pants_for_Birds_ADSBee_1090_P1090-if00", tty_target=u.dev.path)
    yield u
    u.close()


def test_run_unit_console_receiver(fake_unit):
    r = Adsbee1090U(ReceiverConfig("b", "adsbee_1090u", "P1090"), Bench())
    recs, logs = [], []
    summary = rid.run_unit(r, rid.Role(rx=rid.BLE), "ADSBEEBENCHB", "ADSBEEBENCHA", time.time() + 0.5, 2.0,
                           window_s=1.0, emit=recs.append, log=logs.append)
    assert summary["errors"] == [], logs
    wins = [x for x in recs if x["ev"] == "window"]
    assert len(wins) == 2
    assert all(w["rid_reports"] > 0 and w["heap_min_kb"] == 64 for w in wins)
    status = next(x for x in recs if x["ev"] == "status")
    assert status["rx_status"] == ["BT_SCANNING", "BT5_LR_SCANNING"]
    # Found state put back: receive off, console protocol and log level as found, never saved.
    assert fake_unit.state == {"rx": "0", "tx": "0", "log": "WARNINGS", "proto": "MAVLINK1"}
    assert summary["config_hash_restored"] and summary["restore_failed"] == []
    assert "AT+SETTINGS=SAVE" not in fake_unit.dev.received


def test_run_unit_refuses_position_broadcast(fake_unit):
    fake_unit.replies["AT+RX_POSITION?"] = "Receiver Position:\r\n\tSource: FIXED [OK]"
    r = Adsbee1090U(ReceiverConfig("a", "adsbee_1090u", "P1090"), Bench())
    recs = []
    summary = rid.run_unit(r, rid.Role(tx="BT4"), "ADSBEEBENCHA", None, time.time(), 1.0, window_s=1.0,
                           emit=recs.append, log=lambda m: None)
    assert any("broadcast this unit's position" in e for e in summary["errors"])
    assert not any(c.startswith("AT+REMOTE_ID_TX=1") for c in fake_unit.dev.received)
