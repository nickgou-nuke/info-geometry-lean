#!/usr/bin/env python3
"""Nuclear-chart square calibration around the 31P/31S mirror pair.

The default plaquette is

    31P(Z=15,N=16) ---- 32S(Z=16,N=16)
          |                    |
    30P(Z=15,N=15) ---- 31S(Z=16,N=15)

CSV input schema:

    nucleus,z,n,label,energy_keV,n_plus,n_minus,j2,k2,p

The fit extends the mirror-pair band model with chart-square coordinates:

    E = band_terms + z_slope dz + n_slope dn + zn_coupling dz dn

where `dz = Z-15`, `dn = N-15`.  The mixed term is the discrete plaquette
curvature: the residual proton-neutron coupling across the square.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np

from mirror_valence_pair_calibration import coriolis_signature, delta_k_half
from valence_pair_energy_levels import SpectroscopyState


@dataclass(frozen=True)
class SquareLevel:
    nucleus: str
    z: int
    n: int
    label: str
    energy_keV: float
    state: SpectroscopyState


def design_row(level: SquareLevel) -> list[float]:
    s = level.state
    j = s.J
    k = s.K
    dz = level.z - 15
    dn = level.n - 15
    cor = coriolis_signature(s.j2) * float(j + 0.5) * delta_k_half(s.k2)
    return [
        1.0,
        float(s.n_plus + s.n_minus),
        float(j * (j + 1)),
        float(k * k),
        cor,
        float(dz),
        float(dn),
        float(dz * dn),
    ]


PARAM_NAMES = ["E0", "omega", "A", "C", "cor_scale", "z_slope", "n_slope", "zn_coupling"]


def fit_square_constants(levels: list[SquareLevel]) -> tuple[dict[str, float], np.ndarray]:
    x = np.asarray([design_row(level) for level in levels], dtype=float)
    y = np.asarray([level.energy_keV for level in levels], dtype=float)
    coeffs, *_ = np.linalg.lstsq(x, y, rcond=None)
    params = dict(zip(PARAM_NAMES, coeffs))
    return params, y - x @ coeffs


def predict_level(params: dict[str, float], level: SquareLevel) -> float:
    return float(np.asarray(design_row(level)) @ np.asarray([params[name] for name in PARAM_NAMES]))


def read_levels(path: Path) -> list[SquareLevel]:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"nucleus", "z", "n", "label", "energy_keV", "n_plus", "n_minus", "j2", "k2", "p"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise ValueError(f"{path} is missing CSV columns: {sorted(missing)}")
        levels = []
        for row in reader:
            state = SpectroscopyState(
                row["label"],
                int(row["n_plus"]),
                int(row["n_minus"]),
                int(row["j2"]),
                int(row["k2"]),
                int(row["p"]),
            )
            levels.append(
                SquareLevel(
                    row["nucleus"],
                    int(row["z"]),
                    int(row["n"]),
                    row["label"],
                    float(row["energy_keV"]),
                    state,
                )
            )
        return levels


def demo_levels() -> list[SquareLevel]:
    """Rough runnable scaffold, not an adopted nuclear-data table."""

    rows = [
        ("30P", 15, 15, "1+_g", 0.0, 0, 0, 2, 2, 2),
        ("30P", 15, 15, "2+_1", 677.0, 1, 0, 4, 2, 2),
        ("31P", 15, 16, "1/2+_g", 0.0, 0, 0, 1, 1, 2),
        ("31P", 15, 16, "3/2+_1", 1266.0, 1, 0, 3, 1, 2),
        ("31S", 16, 15, "1/2+_g", 0.0, 0, 0, 1, 1, 2),
        ("31S", 16, 15, "3/2+_1", 1249.0, 1, 0, 3, 1, 2),
        ("32S", 16, 16, "0+_g", 0.0, 0, 0, 0, 0, 2),
        ("32S", 16, 16, "2+_1", 2230.0, 1, 1, 4, 0, 2),
    ]
    return [
        SquareLevel(nucleus, z, n, label, energy, SpectroscopyState(label, n_plus, n_minus, j2, k2, p))
        for nucleus, z, n, label, energy, n_plus, n_minus, j2, k2, p in rows
    ]


def plaquette_curvatures(levels: Iterable[SquareLevel], params: dict[str, float]) -> list[tuple[str, float, float]]:
    by_label: dict[str, dict[tuple[int, int], SquareLevel]] = {}
    for level in levels:
        by_label.setdefault(level.label, {})[(level.z, level.n)] = level

    rows = []
    for label, square in sorted(by_label.items()):
        keys = [(15, 15), (16, 15), (15, 16), (16, 16)]
        if all(key in square for key in keys):
            e00, e10, e01, e11 = [square[key].energy_keV for key in keys]
            p00, p10, p01, p11 = [predict_level(params, square[key]) for key in keys]
            rows.append((label, e11 - e10 - e01 + e00, p11 - p10 - p01 + p00))
    return rows


def square_vertex_hamiltonian(params: dict[str, float], levels: list[SquareLevel]) -> tuple[list[str], np.ndarray, np.ndarray]:
    ground_by_vertex: dict[tuple[int, int], SquareLevel] = {}
    for level in levels:
        key = (level.z, level.n)
        if key not in ground_by_vertex or level.energy_keV < ground_by_vertex[key].energy_keV:
            ground_by_vertex[key] = level

    vertices = [(15, 15), (16, 15), (15, 16), (16, 16)]
    labels = [ground_by_vertex[v].nucleus for v in vertices]
    diagonal = [predict_level(params, ground_by_vertex[v]) for v in vertices]

    coupling = max(abs(params["zn_coupling"]), 1.0)
    h = np.diag(diagonal)
    edges = [(0, 1), (0, 2), (1, 3), (2, 3)]
    diagonals = [(0, 3), (1, 2)]
    for i, j in edges:
        h[i, j] = h[j, i] = coupling
    for i, j in diagonals:
        h[i, j] = h[j, i] = 0.5 * coupling
    return labels, h, np.linalg.eigvalsh(h)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, help="CSV file with adopted square levels")
    args = parser.parse_args()

    levels = read_levels(args.data) if args.data else demo_levels()
    source = str(args.data) if args.data else "built-in square demonstration scaffold"
    params, residuals = fit_square_constants(levels)
    rms = float(np.sqrt(np.mean(residuals**2)))

    print("source =", source)
    print("fitted square constants (keV units):")
    for name in PARAM_NAMES:
        print(f"  {name:12s} {params[name]: .6f}")
    print(f"RMS residual = {rms:.6f} keV")

    print("\nlevel audit:")
    for level, residual in zip(levels, residuals):
        pred = predict_level(params, level)
        print(
            f"  {level.nucleus:3s} Z={level.z:2d} N={level.n:2d} {level.label:8s} "
            f"obs={level.energy_keV:9.3f} pred={pred:9.3f} resid={residual:9.3f}"
        )

    curvatures = plaquette_curvatures(levels, params)
    print("\nplaquette curvatures E11-E10-E01+E00:")
    if curvatures:
        for label, observed, predicted in curvatures:
            print(f"  {label:8s} observed={observed:9.3f} predicted={predicted:9.3f}")
    else:
        print("  no label is present at all four square vertices")
    print(f"  fitted mixed square coupling zn_coupling={params['zn_coupling']:.6f}")

    labels, hamiltonian, eigenvalues = square_vertex_hamiltonian(params, levels)
    print("\nsquare vertex basis =", labels)
    print("square Hamiltonian (keV):")
    print(np.array2string(hamiltonian, precision=3, suppress_small=True))
    print("square eigenlevels (keV):")
    for value in eigenvalues:
        print(f"  {value: .6f}")

    assert np.allclose(hamiltonian, hamiltonian.T)
    print("\nnuclear_chart_square_calibration.py: chart-square calibration passed")


if __name__ == "__main__":
    main()
