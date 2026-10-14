"""Receiver oscillator model: maps true time to the receiver's tick counter."""

from dataclasses import dataclass, field

import numpy as np


@dataclass
class Clock:
    """Free-running counter of a receiver.

    Local time is true time plus: a constant offset, a constant frequency error, a frequency random walk (oscillator
    aging and temperature), an optional sinusoidal frequency wander (for example a heating cycle), and phase steps.
    A reset restarts the counter at zero, as after a reboot.
    """

    clock_hz: float = 48e6
    offset_s: float = 0.0  # Local time at true time 0.
    ppm: float = 0.0  # Constant frequency error.
    random_walk_ppm: float = 0.002  # Standard deviation of the frequency change after 1 s, in ppm.
    wander_ppm: float = 0.0  # Amplitude of a sinusoidal frequency wander.
    wander_period_s: float = 900.0
    steps: list = field(default_factory=list)  # [(true time s, phase step s)]
    resets: list = field(default_factory=list)  # [true time s]
    grid_s: float = 0.05  # Resolution of the random walk.
    seed: int = 0

    def __post_init__(self):
        self._rng = np.random.default_rng(self.seed)
        self._freq = np.zeros(1)  # Fractional frequency error of the random walk at grid points.
        self._phase = np.zeros(1)  # Integrated random walk (seconds) at grid points.
        self._wander_phase = self._rng.uniform(0, 2 * np.pi)

    def _extend(self, t_max: float):
        n_needed = int(np.ceil(t_max / self.grid_s)) + 2
        n_have = len(self._freq)
        if n_needed <= n_have:
            return
        n_new = max(n_needed - n_have, 4096)
        steps = self._rng.normal(0, self.random_walk_ppm * 1e-6 * np.sqrt(self.grid_s), n_new)
        freq = self._freq[-1] + np.cumsum(steps)
        phase = self._phase[-1] + np.cumsum((np.concatenate([[self._freq[-1]], freq[:-1]]) + freq) / 2 * self.grid_s)
        self._freq = np.concatenate([self._freq, freq])
        self._phase = np.concatenate([self._phase, phase])

    def local_time(self, t):
        """Local time (seconds since the last counter reset) at true times t >= 0."""
        t = np.asarray(t, dtype=float)
        self._extend(float(np.max(t)) if t.size else 0.0)
        local = self._local_unreset(t)
        for t_reset in sorted(self.resets):
            after = t >= t_reset
            local = np.where(after, local - self._local_unreset(np.float64(t_reset)), local)
        return local

    def _local_unreset(self, t):
        local = t + self.offset_s + self.ppm * 1e-6 * t + np.interp(t / self.grid_s, np.arange(len(self._phase)), self._phase)
        if self.wander_ppm:
            w = 2 * np.pi / self.wander_period_s
            local = local + self.wander_ppm * 1e-6 / w * (np.sin(w * t + self._wander_phase) - np.sin(self._wander_phase))
        for t_step, step_s in self.steps:
            local = local + np.where(t >= t_step, step_s, 0.0)
        return local

    def ticks(self, t):
        """Counter value (int64) at true times t."""
        return np.floor(self.local_time(t) * self.clock_hz).astype(np.int64)
