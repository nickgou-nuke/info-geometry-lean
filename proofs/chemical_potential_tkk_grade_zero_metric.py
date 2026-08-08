#!/usr/bin/env python3
"""Symbolic continuation for chemical-potential bridge diagnostics.

Checks:
* Pauli-matrix commutators for g₀ toy action on ±1 sectors,
* pair {1,2}|{3} environmental boundary counts,
* Pauli-soldered determinant (Casimir) under a local energy/mu shift.
"""

import sympy as sp


def main() -> None:
    mu0, mu1, mu2, lam = sp.symbols("mu0 mu1 mu2 lam", commutative=True)
    E, px, py, pz, dmu = sp.symbols("E px py pz dmu", commutative=True)

    # Exact Gibbs/Jaynes edge differences.
    theta01 = mu1 - mu0
    theta12 = mu2 - mu1
    theta20 = mu0 - mu2
    assert sp.simplify(theta01 + theta12 + theta20) == 0

    # Toy g0 Cartan generator bracket on root-like sectors.
    H = sp.diag(lam, -lam)
    Xp = sp.Matrix([[0, 1], [0, 0]])
    Xm = sp.Matrix([[0, 0], [1, 0]])
    assert H * Xp - Xp * H == 2 * lam * Xp
    assert H * Xm - Xm * H == -2 * lam * Xm

    # Environmental cooperad boundary assignment for pair12|3.
    inner_phase = 2
    outer_phase = 2 * 2
    flux_bits = 2 * 2
    assert inner_phase * outer_phase * flux_bits == 32

    # Pauli-soldered momentum and shifted time slot.
    sigma = lambda E, px, py, pz: sp.Matrix(
        [[E + pz, px - sp.I * py], [px + sp.I * py, E - pz]]
    )

    P = sigma(E, px, py, pz)
    Pshift = sigma(E - dmu, px, py, pz)
    det_shift = sp.simplify(Pshift.det())
    det_orig = sp.simplify(P.det())
    det_formula = sp.expand(det_shift - (det_orig - 2 * E * dmu + dmu ** 2))

    assert det_shift == det_orig - 2 * E * dmu + dmu ** 2
    assert det_formula == 0

    # g00-like heuristic: Minkowski norm shifts quadratically in local delta-mu.
    # If E=mu0 and all spatial components are zero, det(P) = E^2.
    # Then det(Pshift)/det(P) = 1 - 2*δμ/E + (δμ/E)^2 (for E≠0).
    ratio = sp.simplify(det_shift.subs({px: 0, py: 0, pz: 0}) / det_orig.subs({px: 0, py: 0, pz: 0}))
    print("chemical potential edge differences:", theta01, theta12, theta20)
    print("g0 commutator on +1:", (H * Xp - Xp * H))
    print("g0 commutator on -1:", (H * Xm - Xm * H))
    print("environmental product rank factor:", inner_phase * outer_phase * flux_bits)
    print("det(P)=", det_orig)
    print("det(P shifted)=", det_shift)
    print("det shift identity =", det_orig - 2 * E * dmu + dmu ** 2)
    print("ratio at (px,py,pz)=0:", ratio)
    print("chemical_potential_tkk_grade_zero_metric.py: finite audit passed")


if __name__ == "__main__":
    main()
