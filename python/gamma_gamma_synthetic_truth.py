"""Synthetic gamma-gamma coincidence data with an explicit latent graph.

The generator is deliberately separate from the Lean owners.  It provides a
reproducible numerical fixture for downstream Poisson/NMTF experiments:

    Lambda = I_signal * U @ P @ V.T + B
    X ~ Poisson(Lambda)

`levels`, `transitions`, and the detector profiles are exposed so tests and
inference code can inspect the ground truth instead of treating the sample as
an opaque fixture.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import numpy as np


@dataclass(frozen=True)
class DecayTransition:
    source: int
    target: int
    probability: float


class GammaGammaSyntheticTruth:
    """Construct a finite gamma-gamma latent model and Poisson observation."""

    def __init__(
        self,
        num_channels: int = 256,
        energy_max: float = 3000.0,
        resolution: float = 20.0,
        seed: Optional[int] = 0,
    ) -> None:
        if num_channels < 2:
            raise ValueError("num_channels must be at least 2")
        if energy_max <= 0:
            raise ValueError("energy_max must be positive")
        if resolution <= 0:
            raise ValueError("resolution must be positive")
        self.M = int(num_channels)
        self.E_max = float(energy_max)
        self.resolution = float(resolution)
        self.energy_axis = np.linspace(0.0, self.E_max, self.M)
        self.rng = np.random.default_rng(seed)

        self.levels: np.ndarray | None = None
        self.transitions: tuple[DecayTransition, ...] | None = None
        self.E_gamma: np.ndarray | None = None
        self.P_true: np.ndarray | None = None
        self.U_true: np.ndarray | None = None
        self.V_true: np.ndarray | None = None
        self.B_true: np.ndarray | None = None
        self.Lambda_signal: np.ndarray | None = None
        self.Lambda_total: np.ndarray | None = None
        self.X_observed: np.ndarray | None = None

    def generate_decay_logos(self) -> np.ndarray:
        """Install the finite energy-level graph and return transition energies."""
        self.levels = np.array([0.0, 1173.2, 2505.7, 3200.0], dtype=float)
        self.transitions = (
            DecayTransition(2, 1, 0.99),
            DecayTransition(1, 0, 1.00),
            DecayTransition(3, 2, 0.40),
            DecayTransition(3, 1, 0.60),
        )
        self.E_gamma = np.array(
            [self.levels[t.source] - self.levels[t.target] for t in self.transitions],
            dtype=float,
        )
        return self.E_gamma.copy()

    def build_latent_coupling_P(self) -> np.ndarray:
        """Build the symmetric prompt-cascade coupling matrix."""
        if self.transitions is None:
            self.generate_decay_logos()
        assert self.transitions is not None
        n = len(self.transitions)
        P = np.zeros((n, n), dtype=float)
        for i, left in enumerate(self.transitions):
            for j, right in enumerate(self.transitions):
                if left.target == right.source:
                    P[i, j] = left.probability * right.probability
        self.P_true = (P + P.T) / 2.0
        return self.P_true.copy()

    def build_detector_profiles(self, resolution: Optional[float] = None) -> tuple[np.ndarray, np.ndarray]:
        """Build normalized Gaussian response columns for both detectors."""
        if self.E_gamma is None:
            self.generate_decay_logos()
        assert self.E_gamma is not None
        width = self.resolution if resolution is None else float(resolution)
        if width <= 0:
            raise ValueError("resolution must be positive")
        U = np.zeros((self.M, len(self.E_gamma)), dtype=float)
        for i, energy in enumerate(self.E_gamma):
            sigma = width * np.sqrt(energy / 1000.0)
            profile = np.exp(-0.5 * ((self.energy_axis - energy) / sigma) ** 2)
            U[:, i] = profile / profile.sum()
        self.U_true = U
        self.V_true = U.copy()
        return self.U_true.copy(), self.V_true.copy()

    def build_background(self, total_bg_counts: float) -> np.ndarray:
        """Build a normalized separable continuum background."""
        if total_bg_counts < 0:
            raise ValueError("total_bg_counts must be nonnegative")
        scale = self.E_max / 3.0
        bg_1d = np.exp(-self.energy_axis / scale)
        B = np.outer(bg_1d, bg_1d)
        self.B_true = (B / B.sum()) * float(total_bg_counts)
        return self.B_true.copy()

    def generate_observation(self, I_total: float = 1e6, bg_ratio: float = 0.3) -> np.ndarray:
        """Generate deterministic intensity and one seeded Poisson observation."""
        if I_total < 0:
            raise ValueError("I_total must be nonnegative")
        if not 0.0 <= bg_ratio <= 1.0:
            raise ValueError("bg_ratio must lie in [0, 1]")
        self.generate_decay_logos()
        self.build_latent_coupling_P()
        self.build_detector_profiles()
        counts_signal = float(I_total) * (1.0 - bg_ratio)
        self.build_background(float(I_total) * bg_ratio)
        assert self.U_true is not None and self.V_true is not None
        assert self.P_true is not None and self.B_true is not None
        self.Lambda_signal = counts_signal * (self.U_true @ self.P_true @ self.V_true.T)
        self.Lambda_total = self.Lambda_signal + self.B_true
        self.X_observed = self.rng.poisson(self.Lambda_total)
        return self.X_observed.copy()

    def plot_matrix(self) -> None:
        """Display latent coupling, intensity, and log-count matrices."""
        if self.X_observed is None or self.Lambda_total is None or self.P_true is None:
            raise RuntimeError("call generate_observation before plotting")
        import matplotlib.pyplot as plt

        fig, axes = plt.subplots(1, 3, figsize=(18, 5))
        for axis, matrix, title, cmap in (
            (axes[0], self.P_true, "Latent physics (P)", "magma"),
            (axes[1], self.Lambda_total, "Deterministic intensity (Lambda)", "viridis"),
            (axes[2], np.log1p(self.X_observed), "Observed log counts", "inferno"),
        ):
            image = axis.imshow(matrix, origin="lower", cmap=cmap)
            axis.set_title(title)
            fig.colorbar(image, ax=axis)
        fig.tight_layout()
        plt.show()


if __name__ == "__main__":
    generator = GammaGammaSyntheticTruth(num_channels=128, energy_max=3500.0, seed=0)
    observed = generator.generate_observation(I_total=5e5, bg_ratio=0.5)
    print(f"generated observation shape={observed.shape}, total={int(observed.sum())}")
