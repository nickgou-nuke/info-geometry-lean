#!/usr/bin/env python3
"""Render finite-temperature free-energy catastrophe surfaces.

This script builds the same robust-regression-style finite Gibbs model described
in the project notes and visualizes the free-energy landscape at:
1) super-critical epsilon
2) critical epsilon
3) sub-critical epsilon

It uses a numerically stable log-sum-exp evaluation for the free energy.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

import numpy as np


def build_dataset(
    seed: int,
    n_samples: int,
    x_min: float,
    x_max: float,
    noise_sigma: float,
    outlier_count: int,
    outlier_shift: float,
    true_a: float,
    true_b: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Generate synthetic quadratic-regression data with shifted outliers."""
    rng = np.random.default_rng(seed)
    x = np.linspace(x_min, x_max, n_samples)
    # Model: y = a*x - b*x^2 + noise
    y = true_a * x - true_b * x**2 + rng.normal(0.0, noise_sigma, n_samples)
    if outlier_count > 0:
        outlier_count = min(outlier_count, n_samples)
        y[-outlier_count:] += outlier_shift
    # Parameter vector theta = (a, b), design columns [x, -x^2]
    X = np.column_stack([x, -x**2])
    return x, y, X


def free_energy_surface(
    theta_grid: np.ndarray,
    X: np.ndarray,
    y: np.ndarray,
    eps: float,
) -> np.ndarray:
    """Compute free-energy surface F(theta; eps) over a 2D parameter grid."""
    # preds shape: (..., m), where m = number of observations.
    preds = np.einsum("...k,mk->...m", theta_grid, X)
    residuals = y - preds
    energies = 0.5 * residuals**2

    # Stable log-sum-exp:
    # F = -eps * log(sum(exp(-E/eps)))
    #   = -eps * (log(sum(exp(-(E-Emin)/eps))) - Emin/eps)
    #   = -eps * log(sum(...)) + Emin
    min_e = np.min(energies, axis=-1, keepdims=True)
    exp_term = np.exp(-(energies - min_e) / eps)
    z = np.sum(exp_term, axis=-1)
    return -eps * np.log(z) + np.squeeze(min_e, axis=-1)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Render fold-catastrophe free-energy surfaces for three epsilon stages."
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--n-samples", type=int, default=50)
    parser.add_argument("--noise-sigma", type=float, default=0.2)
    parser.add_argument("--outlier-count", type=int, default=15)
    parser.add_argument("--outlier-shift", type=float, default=15.0)
    parser.add_argument("--true-a", type=float, default=10.0)
    parser.add_argument("--true-b", type=float, default=2.0)
    parser.add_argument("--x-min", type=float, default=1.0)
    parser.add_argument("--x-max", type=float, default=5.0)

    parser.add_argument("--a-min", type=float, default=5.0)
    parser.add_argument("--a-max", type=float, default=18.0)
    parser.add_argument("--b-min", type=float, default=0.0)
    parser.add_argument("--b-max", type=float, default=5.0)
    parser.add_argument("--grid-size", type=int, default=100)

    parser.add_argument("--eps-super", type=float, default=100.0)
    parser.add_argument("--eps-critical", type=float, default=21.0)
    parser.add_argument("--eps-sub", type=float, default=5.0)

    parser.add_argument(
        "--save",
        type=Path,
        default=Path("catastrophe_surface.png"),
        help="Output image path (default: catastrophe_surface.png)",
    )
    parser.add_argument(
        "--show",
        action="store_true",
        help="Show interactive window (requires GUI backend).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    try:
        import matplotlib

        if not args.show:
            matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ModuleNotFoundError:
        print(
            "Missing dependency: matplotlib. Install with:\n"
            "  python3 -m pip install matplotlib",
            file=sys.stderr,
        )
        return 1

    _, y, X = build_dataset(
        seed=args.seed,
        n_samples=args.n_samples,
        x_min=args.x_min,
        x_max=args.x_max,
        noise_sigma=args.noise_sigma,
        outlier_count=args.outlier_count,
        outlier_shift=args.outlier_shift,
        true_a=args.true_a,
        true_b=args.true_b,
    )

    a_vals = np.linspace(args.a_min, args.a_max, args.grid_size)
    b_vals = np.linspace(args.b_min, args.b_max, args.grid_size)
    aa, bb = np.meshgrid(a_vals, b_vals)
    theta_grid = np.stack([aa, bb], axis=-1)

    stages = [
        (args.eps_super, "Super-Critical (Gaussian Phase)"),
        (args.eps_critical, "Critical Point (Fold Singularity)"),
        (args.eps_sub, "Sub-Critical (Broken Symmetry)"),
    ]

    fig = plt.figure(figsize=(20, 6))
    for idx, (eps, title) in enumerate(stages, start=1):
        ax = fig.add_subplot(1, 3, idx, projection="3d")
        f_surface = free_energy_surface(theta_grid, X, y, eps)
        f_norm = f_surface - np.min(f_surface)

        ax.plot_surface(aa, bb, f_norm, cmap="magma", edgecolor="none", alpha=0.9)
        ax.scatter([args.true_a], [args.true_b], [0.0], color="cyan", s=80)
        ax.set_title(f"eps={eps:g}\n{title}")
        ax.set_xlabel("a")
        ax.set_ylabel("b")
        ax.set_zlabel("Free Energy (shifted)")
        ax.view_init(elev=40, azim=-110)

    fig.tight_layout()

    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.save, dpi=180)
        print(f"Saved figure to {args.save}")

    if args.show:
        plt.show()
    else:
        plt.close(fig)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
