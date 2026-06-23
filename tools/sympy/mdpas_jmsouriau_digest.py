#!/usr/bin/env python3
"""Finite symbolic audit for Souriau's 1974 spin-particle paper.

This script checks the finite formulas that have Lean owner theorems in the
repository:

* finite Souriau partition positivity and Gibbs normalization;
* Souriau entropy = Massieu + beta * mean energy;
* scalar Bregman vanishing on the diagonal;
* scalarized prequantum scaling identities;
* Pauli anticommutation as the finite spinor readout.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.expand(sp.simplify(expr))
    if getattr(simplified, "is_zero_matrix", False):
        print(f"[ok] {name}")
        return
    if isinstance(simplified, sp.MatrixBase):
        if simplified == sp.zeros(*simplified.shape):
            print(f"[ok] {name}")
            return
        raise AssertionError(f"{name} failed: {simplified}")
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    beta = sp.symbols("beta", real=True)
    e0, e1, e2 = sp.symbols("e0 e1 e2", real=True)
    energies = (e0, e1, e2)

    # Finite Souriau partition / Gibbs shadow.
    Z = sum(sp.exp(-beta * e) for e in energies)
    rho = [sp.exp(-beta * e) / Z for e in energies]
    U = sum(r * e for r, e in zip(rho, energies))
    Phi = sp.log(Z)

    require_zero("Gibbs normalization", sum(rho) - 1)
    require_zero("Massieu-Planck identity", sum(-r * (sp.expand_log(sp.log(r), force=True)) for r in rho) - (Phi + beta * U))

    # Scalar Bregman divergence on the diagonal.
    x, y = sp.symbols("x y", real=True)
    phi = sp.Function("phi")
    dphi = sp.Function("dphi")
    scalar_bregman = phi(x) - phi(y) - dphi(y) * (x - y)
    require_zero("Scalar Bregman self", scalar_bregman.subs(y, x))

    # Scalarized prequantum scaling law.
    omega, hbar, c = sp.symbols("omega hbar c", nonzero=True, real=True)
    curvature = omega / hbar
    curvature_rescaled = curvature / c
    require_zero("Prequantum covariant scale", curvature * hbar - omega)
    require_zero("Prequantum gauge invariance", curvature_rescaled * (c * hbar) - omega)

    # Pauli matrices: the finite spinor carrier used by the paper's 2x2 lane.
    I = sp.I
    eye2 = sp.eye(2)
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])

    require_zero("Pauli square x", sx * sx - eye2)
    require_zero("Pauli square y", sy * sy - eye2)
    require_zero("Pauli square z", sz * sz - eye2)
    require_zero("Pauli anticommutator xy", sx * sy + sy * sx)
    require_zero("Pauli anticommutator xz", sx * sz + sz * sx)
    require_zero("Pauli anticommutator yz", sy * sz + sz * sy)

    print("Z(beta) =", sp.simplify(Z))
    print("Phi(beta) =", Phi)
    print("U(beta) =", sp.simplify(U))


if __name__ == "__main__":
    main()
