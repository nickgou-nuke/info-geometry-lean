#!/usr/bin/env python3
"""Chapter 7 companion: explicit Fibonacci F/R matrix checks."""

from __future__ import annotations

import sympy as sp

from common import check, mat_eq, scalar_eq


def run() -> None:
    print("Chapter 7: explicit F and R finite shadow")
    phi = (1 + sp.sqrt(5)) / 2
    tau = 1 / phi
    s = 1 / sp.sqrt(phi)
    F = sp.Matrix([[tau, s], [s, -tau]])
    R = sp.diag(sp.exp(-4 * sp.pi * sp.I / 5), sp.exp(3 * sp.pi * sp.I / 5))
    B = F * R * F

    check("tau = phi^-1 satisfies tau^2 + tau = 1", scalar_eq(tau**2 + tau, 1))
    check("s^2 = tau", scalar_eq(s**2, tau))
    check("F^2 = I", mat_eq(F * F, sp.eye(2)))
    check("det(F) = -1", scalar_eq(F.det(), -1))
    check("R first phase has unit modulus", scalar_eq(R[0, 0] * sp.conjugate(R[0, 0]), 1))
    check("R second phase has unit modulus", scalar_eq(R[1, 1] * sp.conjugate(R[1, 1]), 1))
    check("B = F R F is definitionally computed", mat_eq(B, F * R * F))


if __name__ == "__main__":
    run()
