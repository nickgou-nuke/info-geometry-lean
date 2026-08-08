#!/usr/bin/env python3
"""Painleve-like exceptional-point cutoff visualization.

This is a numerical witness, not a proof of Painleve III asymptotics.  It plots a
simple non-Hermitian/Klein-twist toy model comparing the divergent bosonic
barrier ``-log |det A|`` with a Super-Berezinian-style stabilized barrier.

The theorem-honest Lean anchors live in:

* ``InformationGeometricCutoff.lean`` for scalar cutoff/phase-volume facts;
* ``SuperBerezinianKlein.lean`` for scalar SBer and glide identities;
* ``GlideSymmetricInvariant.lean`` for finite glide-sector preservation.
"""

from __future__ import annotations

from pathlib import Path
from shutil import which

import subprocess

import numpy as np


EPS = 1.0e-15


def painleve_like_asymptotics(r: float, theta: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Toy critical spectral behavior around an exceptional point.

    ``r`` is distance from the exceptional point; ``theta`` is the Klein-twist
    boundary parameter.  The two eigenvalue sheets are arranged so the bosonic
    determinant collapses at the high-symmetry twist angles.
    """

    lam_plus = np.exp(r) * np.cos(theta)
    lam_minus = np.exp(-r) * np.sin(theta)
    return lam_plus, lam_minus


def stabilized_sber(det_a: np.ndarray, det_d: np.ndarray, coupling: float) -> np.ndarray:
    """Super-Berezinian-style stabilizer.

    The expression models ``det(A - B D^{-1} C) / det(D)`` by adding a positive
    zero-mode correction to the bosonic determinant.  It is deliberately finite
    dimensional and numerical.
    """

    effective_boson = det_a + coupling / (det_d + EPS)
    return effective_boson / (det_d + EPS)


def main() -> None:
    out = Path(__file__).with_name("painleve_transition_stabilization.png")
    data_out = Path(__file__).with_name("painleve_transition_stabilization.csv")

    thetas = np.linspace(0.0, 2.0 * np.pi, 500)
    r_critical = 0.01
    coupling = 0.005

    lam_p, lam_m = painleve_like_asymptotics(r_critical, thetas)

    # Bosonic determinant collapses at theta = 0, pi, 2pi in the toy BZ scan.
    det_a = lam_p * (np.sin(thetas) ** 2)
    det_d = lam_m + 0.1

    sber = stabilized_sber(det_a, det_d, coupling=coupling)

    unregulated_barrier = -np.log(np.abs(det_a) + EPS)
    sber_barrier = -np.log(np.abs(sber) + EPS)

    data = np.column_stack([thetas, unregulated_barrier, sber_barrier])
    np.savetxt(
        data_out,
        data,
        delimiter=",",
        header="theta,unregulated_barrier,sber_style_barrier",
        comments="",
    )

    if which("gnuplot") is None:
        # Matplotlib fallback for environments without gnuplot installed.
        try:
            import matplotlib.pyplot as plt

            plt.figure(figsize=(12, 8))
            plt.plot(thetas, unregulated_barrier, color="red", linestyle="--", linewidth=2, label="unregulated bosonic barrier -log|det A|")
            plt.plot(thetas, sber_barrier, color="blue", linewidth=2.5, label="SBer-style stabilized barrier -log|SBer|")
            plt.axhline(-np.log(EPS), color="gray", linestyle=":", linewidth=1.5, label="numerical divergence cap")
            plt.title("Painleve-like Spectral Transition & Super-Krein Stabilization")
            plt.xlabel("Klein-bottle twist angle theta")
            plt.ylabel("thermodynamic barrier potential")
            plt.ylim(0, 25)
            plt.grid(True)
            plt.legend()
            plt.tight_layout()
            plt.savefig(out)
            plt.close()
        except Exception as exc:
            raise RuntimeError(f"Failed to render fallback figure: {exc}")
    else:
        gnuplot = f"""
set terminal pngcairo size 1800,1080 enhanced font 'Arial,18'
set output '{out}'
set datafile separator ','
set title 'Painleve-like Spectral Transition & Super-Krein Stabilization'
set xlabel 'Klein-bottle twist angle theta'
set ylabel 'thermodynamic barrier potential'
set grid
set key right top
set yrange [0:25]
set style line 1 lc rgb 'red' dt 2 lw 3
set style line 2 lc rgb 'blue' lw 4
set style line 3 lc rgb 'gray' dt 3 lw 2
plot '{data_out}' using 1:2 every ::1 with lines linestyle 1 title 'unregulated bosonic barrier -log|det A|', \\
     '{data_out}' using 1:3 every ::1 with lines linestyle 2 title 'SBer-style stabilized barrier -log|SBer|', \\
     {-np.log(EPS)} with lines linestyle 3 title 'numerical divergence cap'
"""
        subprocess.run(["gnuplot"], input=gnuplot, text=True, check=True)

    print(f"plot: {out}")
    print(f"data: {data_out}")
    print(f"max unregulated barrier: {float(np.max(unregulated_barrier)):.6f}")
    print(f"max SBer-style barrier: {float(np.max(sber_barrier)):.6f}")
    print("numerical witness: SBer-style regularization remains finite in this toy model")


if __name__ == "__main__":
    main()
