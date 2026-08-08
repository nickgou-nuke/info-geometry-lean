#!/usr/bin/env python3
"""Valence-pair energy-level simulator.

This finite model uses the Goutev--Tonev Hamiltonian as the single-valence
energy generator, adds pair binding and Coulomb/mirror offsets, then
diagonalizes a small pair-mixing Hamiltonian.

It is meant for exploratory spectroscopy: replace the toy parameters with
fitted shell-model data when available.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class SpectroscopyState:
    label: str
    n_plus: int
    n_minus: int
    j2: int
    k2: int
    generation_prime: int

    @property
    def J(self) -> sp.Rational:
        return sp.Rational(self.j2, 2)

    @property
    def K(self) -> sp.Rational:
        return sp.Rational(self.k2, 2)


@dataclass(frozen=True)
class ValencePair:
    label: str
    left_kind: str
    right_kind: str
    left_state: SpectroscopyState
    right_state: SpectroscopyState
    pairing_binding: sp.Rational


def topological_gap(chi_s3, z_klein, p):
    return sp.Abs(chi_s3) / z_klein * sp.log(p)


def vibrational_energy(hbar, omega_vac, s: SpectroscopyState):
    return hbar * omega_vac * (s.n_plus + s.n_minus + 1)


def rotational_energy(A, s: SpectroscopyState):
    return A * (s.J * (s.J + 1) - s.K**2)


def coriolis_signature(j2: int) -> int:
    return 1 if (j2 + 1) % 4 == 0 else -1


def delta_k_half(k2: int) -> int:
    return 1 if k2 == 1 else 0


def coriolis_energy(a, inertia_scale, s: SpectroscopyState):
    return (
        coriolis_signature(s.j2)
        * a
        * inertia_scale
        * (s.J + sp.Rational(1, 2))
        * delta_k_half(s.k2)
    )


def single_energy(params, s: SpectroscopyState):
    return (
        topological_gap(params["chi"], params["z_klein"], s.generation_prime)
        + vibrational_energy(params["hbar"], params["omega_vac"], s)
        + rotational_energy(params["A"], s)
        + coriolis_energy(params["decoupling"], params["inertia"], s)
    )


def valence_offset(kind: str, coulomb_shift):
    return coulomb_shift if kind == "p" else sp.Integer(0)


def pair_channel(left: str, right: str) -> str:
    if left == "p" and right == "p":
        return "pp"
    if left == "n" and right == "n":
        return "nn"
    return "pn"


def pair_energy(params, pair: ValencePair):
    left = single_energy(params, pair.left_state) + valence_offset(pair.left_kind, params["coulomb"])
    right = single_energy(params, pair.right_state) + valence_offset(pair.right_kind, params["coulomb"])
    return sp.simplify(left + right - pair.pairing_binding)


def fractional_correction(lambda_eff, Xi):
    return sp.simplify(lambda_eff**2 * Xi)


def lie_flow(params):
    return sp.simplify(fractional_correction(params["lambda_eff"], params["Xi"]))


def mixing_strength(params, pair_i: ValencePair, pair_j: ValencePair):
    same_channel = pair_channel(pair_i.left_kind, pair_i.right_kind) == pair_channel(pair_j.left_kind, pair_j.right_kind)
    same_k = pair_i.left_state.k2 == pair_j.left_state.k2
    if same_channel or same_k:
        return sp.simplify(params["mixing"] + lie_flow(params))
    return sp.Integer(0)


def pair_hamiltonian(params, pairs):
    n = len(pairs)
    H = sp.zeros(n, n)
    for i, pair in enumerate(pairs):
        H[i, i] = pair_energy(params, pair)
    for i in range(n):
        for j in range(i + 1, n):
            H[i, j] = H[j, i] = mixing_strength(params, pairs[i], pairs[j])
    return H


def main() -> None:
    params = {
        "chi": sp.Integer(1),
        "z_klein": sp.Integer(6),
        "hbar": sp.Integer(1),
        "omega_vac": sp.Rational(1, 5),
        "A": sp.Rational(1, 20),
        "decoupling": sp.Rational(1, 10),
        "inertia": sp.Rational(1, 4),
        "coulomb": sp.Rational(3, 100),
        "mixing": sp.Rational(1, 50),
        "lambda_eff": sp.Rational(195, 100),
        "Xi": sp.Rational(263, 1_000_000),
    }

    s_ground = SpectroscopyState("g", 0, 0, 1, 1, 2)
    s_overtone = SpectroscopyState("v1", 1, 0, 3, 1, 2)
    s_offband = SpectroscopyState("off", 0, 1, 5, 3, 3)

    pairs = [
        ValencePair("pn_g", "p", "n", s_ground, s_ground, sp.Rational(3, 20)),
        ValencePair("pn_v1", "p", "n", s_ground, s_overtone, sp.Rational(1, 10)),
        ValencePair("pp_g", "p", "p", s_ground, s_ground, sp.Rational(1, 12)),
        ValencePair("nn_off", "n", "n", s_ground, s_offband, sp.Rational(1, 15)),
    ]

    H = pair_hamiltonian(params, pairs)
    assert H == H.T

    labels = [p.label for p in pairs]
    energies = [sp.simplify(H[i, i]) for i in range(len(pairs))]
    eigenvals = H.eigenvals()

    print("basis =", labels)
    print("diagonal pair energies:")
    for label, energy in zip(labels, energies):
        print(f"  {label:8s} {energy}")

    print("\npair Hamiltonian:")
    sp.printing.pprint(H)

    print("\nenergy eigenvalues:")
    for val, mult in eigenvals.items():
        print(" ", sp.N(val, 12), " multiplicity", mult)

    print("\nflow correction =", lie_flow(params))
    print("trace(H) =", sp.simplify(sp.trace(H)))
    assert sp.simplify(sp.trace(H) - sum(energies)) == 0
    print("valence_pair_energy_levels.py: finite pair dynamics audit passed")


if __name__ == "__main__":
    main()
