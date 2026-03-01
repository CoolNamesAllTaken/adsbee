"""
ADSBee Multi-Receiver Monitor
Connects to multiple ADSBee ADS-B receivers via WebSocket and displays metrics.
"""

import asyncio
import json
import threading
import tkinter as tk
from tkinter import ttk, messagebox
from dataclasses import dataclass
from datetime import datetime
from typing import Optional
import websockets
import websockets.exceptions


# ─────────────────────────────────────────────
# Data Model
# ─────────────────────────────────────────────

@dataclass
class ReceiverMetrics:
    """Accumulated metrics for a single receiver."""
    address: str
    name: str = ""

    # Running totals since last reset
    raw_squitter: int = 0
    valid_squitter: int = 0
    raw_ext_squitter: int = 0
    valid_ext_squitter: int = 0
    demods_1090: int = 0

    num_mode_s_aircraft: int = 0
    num_uat_aircraft: int = 0

    last_update: Optional[datetime] = None
    connected: bool = False
    error: str = ""

    def apply_snapshot(self, adm: dict):
        """Add this message's counts directly to running totals."""
        self.raw_squitter       += adm.get("raw_squitter_frames", 0)
        self.valid_squitter     += adm.get("valid_squitter_frames", 0)
        self.raw_ext_squitter   += adm.get("raw_extended_squitter_frames", 0)
        self.valid_ext_squitter += adm.get("valid_extended_squitter_frames", 0)
        self.demods_1090        += adm.get("demods_1090", 0)
        self.num_mode_s_aircraft = adm.get("num_mode_s_aircraft", 0)
        self.num_uat_aircraft    = adm.get("num_uat_aircraft", 0)
        self.last_update         = datetime.now()

    def reset(self):
        """Zero all running totals."""
        self.raw_squitter = 0
        self.valid_squitter = 0
        self.raw_ext_squitter = 0
        self.valid_ext_squitter = 0
        self.demods_1090 = 0

    @property
    def squitter_valid_pct(self) -> float:
        return (self.valid_squitter / self.raw_squitter * 100) if self.raw_squitter else 0.0

    @property
    def ext_squitter_valid_pct(self) -> float:
        return (self.valid_ext_squitter / self.raw_ext_squitter * 100) if self.raw_ext_squitter else 0.0

    @property
    def display_name(self) -> str:
        return self.name if self.name else self.address


# ─────────────────────────────────────────────
# WebSocket Worker
# ─────────────────────────────────────────────

class ReceiverWorker:
    """Manages a single WebSocket connection in a background thread."""

    def __init__(self, metrics: ReceiverMetrics, on_update):
        self.metrics = metrics
        self.on_update = on_update
        self._stop_event = threading.Event()
        self._thread: Optional[threading.Thread] = None

    def start(self):
        self._stop_event.clear()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop_event.set()

    def _run_loop(self):
        asyncio.run(self._connect_loop())

    async def _connect_loop(self):
        addr = self.metrics.address
        if not addr.startswith("ws://") and not addr.startswith("wss://"):
            ws_url = f"ws://{addr}/metrics"
        else:
            ws_url = addr if addr.endswith("/metrics") else addr + "/metrics"

        while not self._stop_event.is_set():
            try:
                async with websockets.connect(ws_url, ping_interval=10, ping_timeout=5) as ws:
                    self.metrics.connected = True
                    self.metrics.error = ""
                    self.on_update()
                    async for message in ws:
                        if self._stop_event.is_set():
                            break
                        try:
                            data = json.loads(message)
                            adm = data.get("aircraft_dictionary_metrics", {})
                            if adm:
                                self.metrics.apply_snapshot(adm)
                                self.on_update()
                        except json.JSONDecodeError:
                            pass
            except (websockets.exceptions.WebSocketException, OSError, ConnectionRefusedError) as e:
                self.metrics.connected = False
                self.metrics.error = str(e)[:80]
                self.on_update()
                for _ in range(50):
                    if self._stop_event.is_set():
                        return
                    await asyncio.sleep(0.1)
            except Exception as e:
                self.metrics.connected = False
                self.metrics.error = f"Unexpected: {str(e)[:60]}"
                self.on_update()
                await asyncio.sleep(5)


# ─────────────────────────────────────────────
# Theme
# ─────────────────────────────────────────────

DARK_BG  = "#0d1117"
PANEL_BG = "#161b22"
BORDER   = "#30363d"
TEXT_PRI = "#e6edf3"
TEXT_SEC = "#8b949e"
ACCENT   = "#58a6ff"
GREEN    = "#3fb950"
RED      = "#f85149"
ORANGE   = "#d29922"
YELLOW   = "#e3b341"


def _pct_color(pct: float) -> str:
    if pct >= 90: return GREEN
    if pct >= 70: return YELLOW
    if pct >= 50: return ORANGE
    return RED


# ─────────────────────────────────────────────
# Styled button (works reliably on macOS)
# ─────────────────────────────────────────────

def make_button(parent, text, bg, fg, command, padx=12, pady=4, bold=False):
    """A tk.Label styled as a clickable button — avoids macOS native button styling."""
    weight = "bold" if bold else "normal"
    lbl = tk.Label(parent, text=text, font=("Courier", 9, weight),
                   bg=bg, fg=fg, padx=padx, pady=pady, cursor="hand2")

    def on_enter(_):  lbl.config(bg=_lighten(bg))
    def on_leave(_):  lbl.config(bg=bg)
    def on_press(_):  command()

    lbl.bind("<Enter>", on_enter)
    lbl.bind("<Leave>", on_leave)
    lbl.bind("<Button-1>", on_press)
    return lbl


def _lighten(hex_color: str) -> str:
    """Lighten a hex color by ~15%."""
    h = hex_color.lstrip("#")
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    r = min(255, int(r * 1.15))
    g = min(255, int(g * 1.15))
    b = min(255, int(b * 1.15))
    return f"#{r:02x}{g:02x}{b:02x}"


# ─────────────────────────────────────────────
# Receiver Card
# ─────────────────────────────────────────────

class ReceiverCard(tk.Frame):
    def __init__(self, parent, metrics: ReceiverMetrics, on_remove, **kwargs):
        super().__init__(parent, bg=PANEL_BG, highlightbackground=BORDER,
                         highlightthickness=1, **kwargs)
        self.metrics = metrics
        self.on_remove = on_remove
        self._build()

    def _build(self):
        # Header
        hdr = tk.Frame(self, bg="#1c2128", padx=10, pady=6)
        hdr.pack(fill=tk.X)

        self.status_dot = tk.Label(hdr, text="●", font=("Courier", 12),
                                   bg="#1c2128", fg=RED)
        self.status_dot.pack(side=tk.LEFT)

        self.title_lbl = tk.Label(hdr, text=self.metrics.display_name,
                                  font=("Courier", 11, "bold"),
                                  bg="#1c2128", fg=TEXT_PRI, anchor="w")
        self.title_lbl.pack(side=tk.LEFT, padx=(6, 0))

        self.addr_lbl = tk.Label(hdr, text=f"  {self.metrics.address}",
                                 font=("Courier", 9), bg="#1c2128", fg=TEXT_SEC)
        self.addr_lbl.pack(side=tk.LEFT)

        rm = make_button(hdr, "✕", "#1c2128", TEXT_SEC, self.on_remove, padx=6, pady=2)
        rm.pack(side=tk.RIGHT, padx=2)

        # Body
        body = tk.Frame(self, bg=PANEL_BG, padx=12, pady=10)
        body.pack(fill=tk.X)

        def row(label, r, show_pct=False):
            tk.Label(body, text=label, font=("Courier", 9),
                     bg=PANEL_BG, fg=TEXT_SEC, anchor="w", width=26
                     ).grid(row=r, column=0, sticky="w", pady=1)
            val = tk.Label(body, text="—", font=("Courier", 10, "bold"),
                           bg=PANEL_BG, fg=TEXT_PRI, anchor="e", width=12)
            val.grid(row=r, column=1, sticky="e", pady=1)
            pct = None
            if show_pct:
                pct = tk.Label(body, text="", font=("Courier", 10),
                               bg=PANEL_BG, fg=TEXT_SEC, anchor="e", width=9)
                pct.grid(row=r, column=2, sticky="e", pady=1, padx=(4, 0))
            else:
                tk.Label(body, text="", bg=PANEL_BG, width=9).grid(row=r, column=2)
            return val, pct

        tk.Label(body, text="SQUITTER", font=("Courier", 8, "bold"),
                 bg=PANEL_BG, fg=ACCENT).grid(row=0, column=0, sticky="w")
        tk.Label(body, text="COUNT", font=("Courier", 8),
                 bg=PANEL_BG, fg=TEXT_SEC).grid(row=0, column=1, sticky="e")
        tk.Label(body, text="VALID %", font=("Courier", 8),
                 bg=PANEL_BG, fg=TEXT_SEC).grid(row=0, column=2, sticky="e", padx=(4, 0))

        tk.Frame(body, bg=BORDER, height=1).grid(row=1, column=0, columnspan=3,
                                                  sticky="ew", pady=(2, 6))

        self.raw_sq_val,   _              = row("Raw squitter frames",   2)
        self.valid_sq_val, self.sq_pct    = row("Valid squitter frames", 3, True)
        self.raw_ext_val,  _              = row("Raw extended squitter", 4)
        self.valid_ext_val,self.ext_pct   = row("Valid extended squitter", 5, True)
        self.demods_val,   _              = row("Demods 1090",           6)

        tk.Frame(body, bg=BORDER, height=1).grid(row=7, column=0, columnspan=3,
                                                  sticky="ew", pady=(6, 4))

        tk.Label(body, text="AIRCRAFT", font=("Courier", 8, "bold"),
                 bg=PANEL_BG, fg=ACCENT).grid(row=8, column=0, sticky="w")
        self.mode_s_val, _ = row("Mode S aircraft", 9)
        self.uat_val,    _ = row("UAT aircraft",    10)

        tk.Frame(body, bg=BORDER, height=1).grid(row=11, column=0, columnspan=3,
                                                  sticky="ew", pady=(6, 4))

        self.update_lbl = tk.Label(body, text="Waiting for data…",
                                   font=("Courier", 8), bg=PANEL_BG, fg=TEXT_SEC, anchor="w")
        self.update_lbl.grid(row=12, column=0, columnspan=2, sticky="w")

        self.error_lbl = tk.Label(body, text="", font=("Courier", 8),
                                  bg=PANEL_BG, fg=RED, anchor="w", wraplength=300)
        self.error_lbl.grid(row=13, column=0, columnspan=3, sticky="w")

    def refresh(self):
        m = self.metrics
        self.status_dot.config(fg=GREEN if m.connected else RED)
        self.title_lbl.config(text=m.display_name)

        if not m.connected:
            self.error_lbl.config(text=m.error or "Connecting…")
            return

        self.error_lbl.config(text="")
        self.raw_sq_val.config(text=f"{m.raw_squitter:,}")
        self.valid_sq_val.config(text=f"{m.valid_squitter:,}")
        pct = m.squitter_valid_pct
        self.sq_pct.config(text=f"{pct:.1f}%", fg=_pct_color(pct))

        self.raw_ext_val.config(text=f"{m.raw_ext_squitter:,}")
        self.valid_ext_val.config(text=f"{m.valid_ext_squitter:,}")
        pct_e = m.ext_squitter_valid_pct
        self.ext_pct.config(text=f"{pct_e:.1f}%", fg=_pct_color(pct_e))

        self.demods_val.config(text=f"{m.demods_1090:,}")
        self.mode_s_val.config(text=f"{m.num_mode_s_aircraft:,}")
        self.uat_val.config(text=f"{m.num_uat_aircraft:,}")

        if m.last_update:
            self.update_lbl.config(text=f"Updated {m.last_update.strftime('%H:%M:%S')}")


# ─────────────────────────────────────────────
# Summary Bar
# ─────────────────────────────────────────────

class SummaryBar(tk.Frame):
    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg=PANEL_BG, highlightbackground=BORDER,
                         highlightthickness=1, padx=14, pady=8, **kwargs)
        tk.Label(self, text="AGGREGATE  ─  ALL RECEIVERS",
                 font=("Courier", 9, "bold"), bg=PANEL_BG, fg=ACCENT
                 ).grid(row=0, column=0, columnspan=6, sticky="w", pady=(0, 6))

        def stat(col, label):
            tk.Label(self, text=label, font=("Courier", 8),
                     bg=PANEL_BG, fg=TEXT_SEC).grid(row=1, column=col, padx=(0, 20), sticky="w")
            val = tk.Label(self, text="—", font=("Courier", 11, "bold"),
                           bg=PANEL_BG, fg=TEXT_PRI)
            val.grid(row=2, column=col, padx=(0, 20), sticky="w")
            return val

        self.raw_sq   = stat(0, "Raw Squitter")
        self.valid_sq = stat(1, "Valid Squitter")
        self.sq_pct   = stat(2, "Squitter Valid %")
        self.raw_ext  = stat(3, "Raw Ext. Squitter")
        self.valid_ext= stat(4, "Valid Ext. Squitter")
        self.ext_pct  = stat(5, "Ext. Squitter Valid %")

    def update(self, all_metrics: list):
        raw_sq   = sum(m.raw_squitter for m in all_metrics)
        valid_sq = sum(m.valid_squitter for m in all_metrics)
        raw_ext  = sum(m.raw_ext_squitter for m in all_metrics)
        valid_ext= sum(m.valid_ext_squitter for m in all_metrics)
        sq_p  = (valid_sq  / raw_sq  * 100) if raw_sq  else 0.0
        ext_p = (valid_ext / raw_ext * 100) if raw_ext else 0.0

        self.raw_sq.config(text=f"{raw_sq:,}")
        self.valid_sq.config(text=f"{valid_sq:,}")
        self.sq_pct.config(text=f"{sq_p:.1f}%",   fg=_pct_color(sq_p))
        self.raw_ext.config(text=f"{raw_ext:,}")
        self.valid_ext.config(text=f"{valid_ext:,}")
        self.ext_pct.config(text=f"{ext_p:.1f}%", fg=_pct_color(ext_p))


# ─────────────────────────────────────────────
# Main Window
# ─────────────────────────────────────────────

class ADSBeeMonitor(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("ADSBee Multi-Receiver Monitor")
        self.configure(bg=DARK_BG)
        self.minsize(500, 300)
        self.geometry("900x700")

        self._receivers: dict[str, tuple[ReceiverMetrics, ReceiverWorker]] = {}
        self._cards: dict[str, ReceiverCard] = {}
        self._selected: set[str] = set()
        self._update_pending = False

        self._build_ui()
        self._schedule_refresh()

    def _build_ui(self):
        # ── Toolbar ───────────────────────────────────────────────────────────
        toolbar = tk.Frame(self, bg="#1c2128", padx=12, pady=8,
                           highlightbackground=BORDER, highlightthickness=1)
        toolbar.pack(fill=tk.X)

        tk.Label(toolbar, text="◈ ADSBee Monitor", font=("Courier", 13, "bold"),
                 bg="#1c2128", fg=ACCENT).pack(side=tk.LEFT)

        make_button(toolbar, "+ Add Receiver", ACCENT, DARK_BG,
                    self._add_receiver_dialog, bold=True
                    ).pack(side=tk.RIGHT, padx=(6, 4))
        make_button(toolbar, "⟳ Reset All", "#238636", "#ffffff",
                    self._reset_all
                    ).pack(side=tk.RIGHT, padx=3)
        make_button(toolbar, "⟳ Reset Selected", "#444c56", TEXT_PRI,
                    self._reset_selected
                    ).pack(side=tk.RIGHT, padx=3)

        # ── Summary bar ───────────────────────────────────────────────────────
        self.summary_bar = SummaryBar(self)
        self.summary_bar.pack(fill=tk.X, padx=10, pady=(10, 0))

        # ── Selection row ─────────────────────────────────────────────────────
        sel_bar = tk.Frame(self, bg=DARK_BG, pady=4)
        sel_bar.pack(fill=tk.X, padx=10)
        tk.Label(sel_bar, text="Select:", font=("Courier", 8),
                 bg=DARK_BG, fg=TEXT_SEC).pack(side=tk.LEFT)
        make_button(sel_bar, "All",  PANEL_BG, TEXT_SEC, self._select_all,  padx=8, pady=2
                    ).pack(side=tk.LEFT, padx=2)
        make_button(sel_bar, "None", PANEL_BG, TEXT_SEC, self._select_none, padx=8, pady=2
                    ).pack(side=tk.LEFT, padx=2)
        self._sel_label = tk.Label(sel_bar, text="", font=("Courier", 8),
                                   bg=DARK_BG, fg=TEXT_SEC)
        self._sel_label.pack(side=tk.LEFT, padx=8)

        # ── Scrollable card area ──────────────────────────────────────────────
        container = tk.Frame(self, bg=DARK_BG)
        container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        canvas = tk.Canvas(container, bg=DARK_BG, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        self._cards_frame = tk.Frame(canvas, bg=DARK_BG)

        self._cards_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=self._cards_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        canvas.bind_all("<MouseWheel>",
                        lambda e: canvas.yview_scroll(int(-1 * (e.delta / 120)), "units"))
        self._canvas = canvas

        # Empty state — on container so it never mixes geometry managers with cards
        self._empty_lbl = tk.Label(
            container,
            text='No receivers added.\nClick "+ Add Receiver" to get started.',
            font=("Courier", 11), bg=DARK_BG, fg=TEXT_SEC, justify="center", pady=60
        )
        self._empty_lbl.place(relx=0.5, rely=0.5, anchor="center")

    # ── Card layout (pack only) ───────────────────────────────────────────────

    def _layout_cards(self):
        for card in self._cards.values():
            card.pack_forget()
        for card in self._cards.values():
            card.pack(fill=tk.X, padx=8, pady=6)

        if self._cards:
            self._empty_lbl.place_forget()
        else:
            self._empty_lbl.place(relx=0.5, rely=0.5, anchor="center")

    def _add_card(self, metrics: ReceiverMetrics):
        card = ReceiverCard(
            self._cards_frame, metrics,
            on_remove=lambda a=metrics.address: self._remove_receiver(a)
        )

        def toggle_sel(event, addr=metrics.address):
            if addr in self._selected:
                self._selected.discard(addr)
                card.config(highlightbackground=BORDER)
            else:
                self._selected.add(addr)
                card.config(highlightbackground=ACCENT)
            self._update_sel_label()

        card.bind("<Button-1>", toggle_sel)
        for child in card.winfo_children():
            child.bind("<Button-1>", toggle_sel)

        self._cards[metrics.address] = card
        self._layout_cards()

    def _remove_card(self, address: str):
        if address in self._cards:
            self._cards[address].destroy()
            del self._cards[address]
        self._selected.discard(address)
        self._layout_cards()
        self._update_sel_label()

    # ── Receiver lifecycle ────────────────────────────────────────────────────

    def _add_receiver_dialog(self):
        dlg = ReceiverDialog(self)
        self.wait_window(dlg)
        if dlg.result:
            addr, name = dlg.result
            self._add_receiver(addr, name)

    def _add_receiver(self, address: str, name: str = ""):
        if address in self._receivers:
            messagebox.showwarning("Duplicate", f"{address} is already added.")
            return
        metrics = ReceiverMetrics(address=address, name=name)
        worker  = ReceiverWorker(metrics, on_update=self._schedule_ui_update)
        self._receivers[address] = (metrics, worker)
        self._add_card(metrics)
        worker.start()

    def _remove_receiver(self, address: str):
        if address in self._receivers:
            _, worker = self._receivers.pop(address)
            worker.stop()
        self._remove_card(address)

    # ── Reset ─────────────────────────────────────────────────────────────────

    def _reset_all(self):
        for metrics, _ in self._receivers.values():
            metrics.reset()
        self._refresh_ui()

    def _reset_selected(self):
        if not self._selected:
            messagebox.showinfo("Reset Selected",
                                "No receivers selected.\nClick a card to select it.")
            return
        for addr in self._selected:
            if addr in self._receivers:
                self._receivers[addr][0].reset()
        self._refresh_ui()

    # ── Selection ─────────────────────────────────────────────────────────────

    def _select_all(self):
        self._selected = set(self._cards.keys())
        for card in self._cards.values():
            card.config(highlightbackground=ACCENT)
        self._update_sel_label()

    def _select_none(self):
        self._selected.clear()
        for card in self._cards.values():
            card.config(highlightbackground=BORDER)
        self._update_sel_label()

    def _update_sel_label(self):
        n = len(self._selected)
        self._sel_label.config(text=f"{n} selected" if n else "")

    # ── UI refresh ────────────────────────────────────────────────────────────

    def _schedule_ui_update(self):
        if not self._update_pending:
            self._update_pending = True
            self.after(0, self._refresh_ui)

    def _schedule_refresh(self):
        self._refresh_ui()
        self.after(2000, self._schedule_refresh)

    def _refresh_ui(self):
        self._update_pending = False
        all_metrics = [m for m, _ in self._receivers.values()]
        self.summary_bar.update(all_metrics)
        for addr, card in self._cards.items():
            if addr in self._receivers:
                card.refresh()

    def on_resize(self, event):
        pass


# ─────────────────────────────────────────────
# Add Receiver Dialog
# ─────────────────────────────────────────────

class ReceiverDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Add Receiver")
        self.configure(bg=DARK_BG)
        self.resizable(False, False)
        self.result = None
        self.grab_set()

        px = dict(padx=16)

        tk.Label(self, text="Add ADS-B Receiver", font=("Courier", 11, "bold"),
                 bg=DARK_BG, fg=ACCENT).pack(**px, pady=(14, 4))

        tk.Label(self, text="IP Address / Hostname", font=("Courier", 9),
                 bg=DARK_BG, fg=TEXT_SEC, anchor="w").pack(fill=tk.X, **px, pady=(8, 0))

        self._addr = tk.Entry(self, font=("Courier", 11), bg=PANEL_BG, fg=TEXT_PRI,
                              insertbackground=TEXT_PRI, relief="flat",
                              highlightbackground=BORDER, highlightthickness=1, width=34)
        self._addr.pack(**px, pady=(0, 4))
        self._addr.insert(0, "192.168.1.")
        self._addr.focus_set()

        tk.Label(self, text="Display Name (optional)", font=("Courier", 9),
                 bg=DARK_BG, fg=TEXT_SEC, anchor="w").pack(fill=tk.X, **px, pady=(4, 0))
        self._name = tk.Entry(self, font=("Courier", 11), bg=PANEL_BG, fg=TEXT_PRI,
                              insertbackground=TEXT_PRI, relief="flat",
                              highlightbackground=BORDER, highlightthickness=1, width=34)
        self._name.pack(**px, pady=(0, 8))

        btn_frame = tk.Frame(self, bg=DARK_BG)
        btn_frame.pack(**px, pady=(4, 14))

        make_button(btn_frame, "Cancel", PANEL_BG, TEXT_SEC,
                    self.destroy, padx=14, pady=4).pack(side=tk.LEFT, padx=(0, 8))
        make_button(btn_frame, "Connect", ACCENT, DARK_BG,
                    self._submit, padx=14, pady=4, bold=True).pack(side=tk.LEFT)

        self.bind("<Return>", lambda e: self._submit())
        self.bind("<Escape>", lambda e: self.destroy())

    def _submit(self):
        addr = self._addr.get().strip()
        if not addr:
            return
        self.result = (addr, self._name.get().strip())
        self.destroy()


# ─────────────────────────────────────────────
# Entry Point
# ─────────────────────────────────────────────

def main():
    app = ADSBeeMonitor()
    app.bind("<Configure>", app.on_resize)
    app.mainloop()


if __name__ == "__main__":
    main()