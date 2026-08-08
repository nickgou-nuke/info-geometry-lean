#!/usr/bin/env python3
"""SU(2)-equivariant valence-pair VQE toy.

This is the local, dependency-light bridge to
`XanaduAI/all-you-need-is-spin`: it uses the same two-qubit Schur matrix as the
upstream `Spin_2` gate, but runs with only NumPy.

The four computational basis states are the four vertices of the nuclear-chart
square Hamiltonian from `nuclear_chart_square_calibration.py`.  The variational
unitary is

    U(θ) = S₂ᵀ diag(1, 1, 1, exp(iθ)) S₂

which is the matrix form of the Xanadu `Spin_2` Schur gate.  We grid-search θ
and compare the variational energy against exact diagonalization.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np

from nuclear_chart_square_calibration import (
    demo_levels,
    fit_square_constants,
    read_levels,
    square_vertex_hamiltonian,
)


def schur2() -> np.ndarray:
    rt2 = np.sqrt(2.0)
    return np.array(
        [
            [1, 0, 0, 0],
            [0, 1 / rt2, 1 / rt2, 0],
            [0, 0, 0, 1],
            [0, 1 / rt2, -1 / rt2, 0],
        ],
        dtype=complex,
    )


def spin2_unitary(theta: float) -> np.ndarray:
    s2 = schur2()
    controlled_phase = np.diag([1.0, 1.0, 1.0, np.exp(1j * theta)])
    return s2.conj().T @ controlled_phase @ s2


def normalized(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=complex)
    return values / np.linalg.norm(values)


def variational_state(theta: float) -> np.ndarray:
    # A deliberately non-eigenvector seed so the Schur phase has a visible
    # variational effect.  This is the "trial beam" through the SU(2) sector.
    seed = normalized(np.array([1.0, 0.7, -0.2, 0.5], dtype=complex))
    return spin2_unitary(theta) @ seed


def energy_expectation(hamiltonian: np.ndarray, state: np.ndarray) -> float:
    return float(np.real(np.vdot(state, hamiltonian @ state)))


def grid_search(hamiltonian: np.ndarray, grid_points: int) -> tuple[float, float, np.ndarray]:
    best_theta = 0.0
    best_energy = float("inf")
    best_state = None
    for theta in np.linspace(0.0, 2.0 * np.pi, grid_points, endpoint=False):
        state = variational_state(theta)
        energy = energy_expectation(hamiltonian, state)
        if energy < best_energy:
            best_theta = float(theta)
            best_energy = energy
            best_state = state
    assert best_state is not None
    return best_theta, best_energy, best_state


def schur_basis_hamiltonian(hamiltonian: np.ndarray) -> np.ndarray:
    s2 = schur2()
    return s2 @ hamiltonian @ s2.conj().T


def singlet_triplet_mixing_norm(hamiltonian: np.ndarray) -> float:
    h_schur = schur_basis_hamiltonian(hamiltonian)
    # In the upstream Spin_2 convention, rows 0,1,2 are triplet-like and row 3
    # is the singlet.  This norm measures how hard the fitted Hamiltonian tries
    # to mix across those sectors.
    return float(np.linalg.norm(h_schur[:3, 3]) + np.linalg.norm(h_schur[3, :3]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, help="CSV file with adopted square levels")
    parser.add_argument("--grid-points", type=int, default=720)
    args = parser.parse_args()

    levels = read_levels(args.data) if args.data else demo_levels()
    params, _ = fit_square_constants(levels)
    labels, hamiltonian, exact_eigenvalues = square_vertex_hamiltonian(params, levels)

    theta, vqe_energy, state = grid_search(hamiltonian, args.grid_points)
    exact_ground = float(exact_eigenvalues[0])
    gap = vqe_energy - exact_ground
    unitary_error = np.linalg.norm(spin2_unitary(theta).conj().T @ spin2_unitary(theta) - np.eye(4))
    sector_mixing = singlet_triplet_mixing_norm(hamiltonian)
    sampled_energies = [
        energy_expectation(hamiltonian, variational_state(theta))
        for theta in np.linspace(0.0, 2.0 * np.pi, args.grid_points, endpoint=False)
    ]

    print("square basis =", labels)
    print("Spin_2 Schur unitary error =", f"{unitary_error:.3e}")
    print("Schur singlet-triplet mixing norm =", f"{sector_mixing:.9f}", "keV")
    print("best theta =", f"{theta:.9f}")
    print("VQE energy =", f"{vqe_energy:.9f}", "keV")
    print("VQE energy range =", f"{min(sampled_energies):.9f}", "to", f"{max(sampled_energies):.9f}", "keV")
    print("exact ground =", f"{exact_ground:.9f}", "keV")
    print("variational excess =", f"{gap:.9f}", "keV")
    print("state probabilities:")
    for label, amp in zip(labels, state):
        print(f"  {label:3s} {abs(amp) ** 2:.9f}")

    assert unitary_error < 1e-12
    assert vqe_energy + 1e-9 >= exact_ground
    assert abs(np.vdot(state, state) - 1.0) < 1e-12
    print("su2_valence_pair_vqe.py: SU(2) valence-pair VQE audit passed")


if __name__ == "__main__":
    main()
