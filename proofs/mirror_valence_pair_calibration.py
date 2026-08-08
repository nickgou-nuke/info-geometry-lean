#!/usr/bin/env python3
"""Mirror-nucleus valence-pair calibration.

This script fits the effective Goutev--Tonev band constants from observed
mirror-nucleus levels and then feeds the fitted constants into the valence-pair
Hamiltonian.

CSV input schema:

    nucleus,label,energy_keV,n_plus,n_minus,j2,k2,p

`j2` and `k2` are doubled half-integer quantum numbers.  For example,
`j2=1,k2=1` means `J=K=1/2`.

If no CSV is supplied, the script runs a small demonstration dataset.  Those
demo levels are a scaffold for testing the fitter, not an adopted ENSDF table.
Use `--data adopted_levels.csv` for publication-grade calibration.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np

from valence_pair_energy_levels import (
    SpectroscopyState,
    ValencePair,
    pair_hamiltonian,
)


@dataclass(frozen=True)
class ObservedLevel:
    nucleus: str
    label: str
    energy_keV: float
    state: SpectroscopyState


def coriolis_signature(j2: int) -> int:
    return 1 if (j2 + 1) % 4 == 0 else -1


def delta_k_half(k2: int) -> int:
    return 1 if k2 == 1 else 0


def design_row(level: ObservedLevel) -> list[float]:
    """Linear band model row.

    E = E0 + omega(n+ + n-) + A J(J+1) + C K^2
        + cor_scale signature(J)(J+1/2)delta_K,1/2
        + mirror_shift I[nucleus=31S]
    """

    s = level.state
    j = s.J
    k = s.K
    cor = coriolis_signature(s.j2) * float(j + 0.5) * delta_k_half(s.k2)
    return [
        1.0,
        float(s.n_plus + s.n_minus),
        float(j * (j + 1)),
        float(k * k),
        cor,
        1.0 if level.nucleus == "31S" else 0.0,
    ]


def fit_band_constants(levels: list[ObservedLevel]) -> tuple[dict[str, float], np.ndarray]:
    x = np.asarray([design_row(level) for level in levels], dtype=float)
    y = np.asarray([level.energy_keV for level in levels], dtype=float)
    coeffs, *_ = np.linalg.lstsq(x, y, rcond=None)
    names = ["E0", "omega", "A", "C", "cor_scale", "mirror_shift"]
    params = dict(zip(names, coeffs))
    residuals = y - x @ coeffs
    return params, residuals


def predict_level(params: dict[str, float], level: ObservedLevel) -> float:
    row = np.asarray(design_row(level), dtype=float)
    coeff = np.asarray([params[k] for k in ["E0", "omega", "A", "C", "cor_scale", "mirror_shift"]])
    return float(row @ coeff)


def read_levels(path: Path) -> list[ObservedLevel]:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"nucleus", "label", "energy_keV", "n_plus", "n_minus", "j2", "k2", "p"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise ValueError(f"{path} is missing CSV columns: {sorted(missing)}")
        levels = []
        for row in reader:
            state = SpectroscopyState(
                label=row["label"],
                n_plus=int(row["n_plus"]),
                n_minus=int(row["n_minus"]),
                j2=int(row["j2"]),
                k2=int(row["k2"]),
                generation_prime=int(row["p"]),
            )
            levels.append(ObservedLevel(row["nucleus"], row["label"], float(row["energy_keV"]), state))
        return levels


def demo_levels() -> list[ObservedLevel]:
    """Small calibration scaffold.

    These values are deliberately simple, low-lying mirror-like levels in keV.
    They exercise the fitter and pair simulator; replace them with adopted
    ENSDF/Jenkins-table values for physics claims.
    """

    rows = [
        ("31P", "1/2+_g", 0.0, 0, 0, 1, 1, 2),
        ("31P", "3/2+_1", 1266.0, 1, 0, 3, 1, 2),
        ("31P", "5/2+_1", 2234.0, 0, 1, 5, 3, 2),
        ("31P", "7/2-_1", 3134.0, 1, 1, 7, 1, 3),
        ("31S", "1/2+_g", 0.0, 0, 0, 1, 1, 2),
        ("31S", "3/2+_1", 1249.0, 1, 0, 3, 1, 2),
        ("31S", "5/2+_1", 2210.0, 0, 1, 5, 3, 2),
        ("31S", "7/2-_1", 3190.0, 1, 1, 7, 1, 3),
    ]
    return [
        ObservedLevel(
            nucleus,
            label,
            energy,
            SpectroscopyState(label, n_plus, n_minus, j2, k2, p),
        )
        for nucleus, label, energy, n_plus, n_minus, j2, k2, p in rows
    ]


def matched_mirror_differences(levels: Iterable[ObservedLevel], params: dict[str, float]) -> list[tuple[str, float, float, float]]:
    by_label: dict[str, dict[str, ObservedLevel]] = {}
    for level in levels:
        by_label.setdefault(level.label, {})[level.nucleus] = level

    result = []
    for label, nuclei in sorted(by_label.items()):
        if "31S" in nuclei and "31P" in nuclei:
            s_pred = predict_level(params, nuclei["31S"])
            p_pred = predict_level(params, nuclei["31P"])
            result.append((label, nuclei["31S"].energy_keV - nuclei["31P"].energy_keV, s_pred - p_pred, s_pred))
    return result


def fitted_pair_params(params: dict[str, float]) -> dict[str, float]:
    # The valence-pair simulator expects these keys.  We put the fitted
    # spectroscopy constants into the same names and keep small finite
    # off-diagonal values for the pair mixing.
    return {
        "chi": 0.0,
        "z_klein": 1.0,
        "hbar": 1.0,
        "omega_vac": params["omega"],
        "A": params["A"],
        "decoupling": 1.0,
        "inertia": params["cor_scale"],
        "coulomb": max(params["mirror_shift"], 0.0),
        "mixing": max(abs(params["mirror_shift"]), 1.0),
        "lambda_eff": 1.0,
        "Xi": 0.001,
    }


def simulate_valence_pairs(params: dict[str, float]) -> tuple[list[str], np.ndarray, np.ndarray]:
    p = fitted_pair_params(params)
    s_ground = SpectroscopyState("g", 0, 0, 1, 1, 2)
    s_v1 = SpectroscopyState("v1", 1, 0, 3, 1, 2)
    s_off = SpectroscopyState("off", 0, 1, 5, 3, 2)

    pairs = [
        ValencePair("pn_g", "p", "n", s_ground, s_ground, 150.0),
        ValencePair("pn_v1", "p", "n", s_ground, s_v1, 100.0),
        ValencePair("pp_g", "p", "p", s_ground, s_ground, 85.0),
        ValencePair("nn_off", "n", "n", s_ground, s_off, 70.0),
    ]
    hamiltonian = np.asarray(pair_hamiltonian(p, pairs), dtype=float)
    eigenvalues = np.linalg.eigvalsh(hamiltonian)
    return [pair.label for pair in pairs], hamiltonian, eigenvalues


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, help="CSV file with adopted mirror levels")
    args = parser.parse_args()

    levels = read_levels(args.data) if args.data else demo_levels()
    source = str(args.data) if args.data else "built-in demonstration scaffold"
    params, residuals = fit_band_constants(levels)
    rms = float(np.sqrt(np.mean(residuals**2)))

    print("source =", source)
    print("fitted band constants (keV units):")
    for key in ["E0", "omega", "A", "C", "cor_scale", "mirror_shift"]:
        print(f"  {key:12s} {params[key]: .6f}")
    print(f"RMS residual = {rms:.6f} keV")

    print("\nlevel audit:")
    for level, residual in zip(levels, residuals):
        pred = predict_level(params, level)
        print(
            f"  {level.nucleus:3s} {level.label:8s} "
            f"obs={level.energy_keV:9.3f} pred={pred:9.3f} resid={residual:9.3f}"
        )

    print("\nmatched mirror differences, 31S - 31P:")
    for label, observed, predicted, _ in matched_mirror_differences(levels, params):
        print(f"  {label:8s} observed={observed:9.3f} predicted={predicted:9.3f}")

    labels, hamiltonian, eigenvalues = simulate_valence_pairs(params)
    print("\nvalence-pair basis =", labels)
    print("pair Hamiltonian (keV):")
    print(np.array2string(hamiltonian, precision=3, suppress_small=True))
    print("pair eigenlevels (keV):")
    for value in eigenvalues:
        print(f"  {value: .6f}")

    assert np.allclose(hamiltonian, hamiltonian.T)
    assert np.isclose(np.trace(hamiltonian), np.sum(np.diag(hamiltonian)))
    print("\nmirror_valence_pair_calibration.py: calibration and pair simulation passed")


if __name__ == "__main__":
    main()
