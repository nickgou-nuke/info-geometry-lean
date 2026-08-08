#!/usr/bin/env python3
"""Non-Hermitian Kitaev--Cuntz / SSH edge-mode simulation.

This is an applied tight-binding witness, not a claim of material realization.
It demonstrates two theorem-honest facts used by the Lean core:

1. A one-sided chiral/Cuntz block has exact zero modes at the cut boundary.
2. A non-reciprocal open chain exhibits skin localization while topological
   edge modes remain the smallest-|E| states in the topological regime.
"""

from __future__ import annotations

import numpy as np


def nh_ssh_chain(n_cells: int, v: float, w_right: float, w_left: float) -> np.ndarray:
    """Open non-Hermitian SSH chain with n_cells A/B sites.

    Basis: A0,B0,A1,B1,...  Intracell coupling v; intercell couplings are
    non-reciprocal: B_j -> A_{j+1} has w_right, A_{j+1} -> B_j has w_left.
    """
    n = 2 * n_cells
    H = np.zeros((n, n), dtype=complex)
    for j in range(n_cells):
        A, B = 2 * j, 2 * j + 1
        H[A, B] = v
        H[B, A] = v
        if j + 1 < n_cells:
            A_next = 2 * (j + 1)
            H[A_next, B] = w_right
            H[B, A_next] = w_left
    return H


def edge_weight(vec: np.ndarray, n_edge_sites: int = 2) -> float:
    prob = np.abs(vec) ** 2
    prob = prob / prob.sum()
    return float(prob[:n_edge_sites].sum() + prob[-n_edge_sites:].sum())


def center_of_mass(vec: np.ndarray) -> float:
    prob = np.abs(vec) ** 2
    prob = prob / prob.sum()
    return float(np.dot(np.arange(len(vec)), prob))


def analyze_case(name: str, n_cells: int, v: float, w_right: float, w_left: float) -> None:
    H = nh_ssh_chain(n_cells, v, w_right, w_left)
    evals, evecs = np.linalg.eig(H)
    order = np.argsort(np.abs(evals))
    print(f"\n{name}")
    print(f"n_cells={n_cells}, v={v:.4f}, w_right={w_right:.4f}, w_left={w_left:.4f}")
    print("smallest |E| eigenvalues:")
    for k in order[:4]:
        ew = edge_weight(evecs[:, k])
        cm = center_of_mass(evecs[:, k])
        print(f"  E={evals[k].real:+.6e}{evals[k].imag:+.6e}j |E|={abs(evals[k]):.3e} edge_weight={ew:.3f} COM={cm:.2f}")

    # Skin-effect diagnostic over bulk-ish states: nonreciprocal chains bias COM.
    coms = np.array([center_of_mass(evecs[:, k]) for k in range(evecs.shape[1])])
    print(f"mean eigenvector center-of-mass = {coms.mean():.3f} / site range [0,{2*n_cells-1}]")


def main() -> int:
    print("Non-Hermitian Kitaev--Cuntz / SSH edge-mode witness")

    # Exact Cuntz/cut limit: v=0 leaves two exact boundary zero modes.
    analyze_case("Exact Cuntz cut: pinned boundary zero modes", n_cells=12, v=0.0, w_right=1.4, w_left=0.6)

    # Topological but weakly coupled edges: exponentially small finite-size splitting.
    analyze_case("Topological nonreciprocal chain: near-zero Majorana/SSH edge pair", n_cells=24, v=0.15, w_right=1.4, w_left=0.6)

    # Trivial regime for comparison: no near-zero edge pair.
    analyze_case("Trivial comparison", n_cells=24, v=1.2, w_right=0.7, w_left=0.5)

    print("\nOK non-Hermitian Kitaev--Cuntz chain witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
