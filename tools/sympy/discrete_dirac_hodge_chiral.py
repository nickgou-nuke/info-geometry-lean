#!/usr/bin/env python3
"""Finite K3/triangle discrete Dirac--Hodge witness.

Uses the filled 2-simplex on three vertices.  The incidence matrices satisfy
  d1*d0 = 0.
On total forms Ω0⊕Ω1⊕Ω2, define d, δ=dᵀ, D=d+δ, L=D².
Checks nilpotence, Dirac-Hodge Laplacian reconstruction, chirality
anticommutation, and absence of harmonic 1-forms for the filled triangle.
"""

import sympy as sp


def assert_zero(M, name):
    if isinstance(M, sp.MatrixBase):
        ok = M == sp.zeros(*M.shape)
        val = M
    else:
        val = sp.simplify(M)
        ok = val == 0
    if not ok:
        raise AssertionError(f"{name} failed: {val}")
    print(f"[ok] {name}")


def main():
    # Oriented edges: 01, 12, 02.  Filled face orientation: 012.
    d0 = sp.Matrix([
        [-1, 1, 0],  # edge 01
        [0, -1, 1],  # edge 12
        [-1, 0, 1],  # edge 02
    ])
    d1 = sp.Matrix([[-1, -1, 1]])  # boundary convention compatible with d1*d0=0

    assert_zero(d1 * d0, "simplicial nilpotence d1*d0")

    Z03 = sp.zeros(3, 3)
    Z31 = sp.zeros(3, 1)
    Z13 = sp.zeros(1, 3)
    Z11 = sp.zeros(1, 1)

    d = sp.Matrix.vstack(
        sp.Matrix.hstack(Z03, Z03, Z31),
        sp.Matrix.hstack(d0, Z03, Z31),
        sp.Matrix.hstack(Z13, d1, Z11),
    )
    delta = d.T
    D = d + delta
    L = D * D
    hodge_L = d * delta + delta * d

    assert_zero(d * d, "total exterior derivative d^2")
    assert_zero(delta * delta, "total codifferential delta^2")
    assert_zero(L - hodge_L, "D^2 = d delta + delta d")

    gamma = sp.diag(1, 1, 1, -1, -1, -1, 1)
    assert_zero(gamma * gamma - sp.eye(7), "chirality involution")
    assert_zero(D * gamma + gamma * D, "Dirac anticommutes with chirality")

    L1 = d1.T * d1 + d0 * d0.T
    assert_zero(L1.det() - 27, "filled triangle one-form Laplacian invertible")

    # Boundary-only K3 cycle: no face term, so the harmonic code vector is the
    # cycle in ker(d0^T), orthogonal to all exact edge gradients im(d0).
    phi0, phi1, phi2 = sp.symbols("phi0 phi1 phi2")
    phi = sp.Matrix([phi0, phi1, phi2])
    cycle = sp.Matrix([1, 1, -1])
    exact = d0 * phi
    assert_zero(d0.T * cycle, "boundary cycle is coclosed / harmonic")
    assert_zero((cycle.T * exact)[0], "harmonic cycle orthogonal to exact errors")
    assert_zero((d1 * cycle)[0] + 3, "filled face detects boundary cycle flux")

    print("d0 =")
    print(d0)
    print("d1 =")
    print(d1)
    print("L1 =")
    print(L1)


if __name__ == "__main__":
    main()
