#!/usr/bin/env python3
"""Chapter 6 companion: Fibonacci fusion ring matrix shadow."""

from __future__ import annotations

import sympy as sp

from common import check, mat_eq, scalar_eq


def run() -> None:
    print("Chapter 6: Fibonacci fusion ring finite shadow")
    phi = (1 + sp.sqrt(5)) / 2
    N_tau = sp.Matrix([[0, 1], [1, 1]])
    one = sp.Matrix([1, 0])
    tau = sp.Matrix([0, 1])

    check("tau * one = tau", mat_eq(N_tau * one, tau))
    check("tau * tau = one + tau", mat_eq(N_tau * tau, one + tau))
    check("phi^2 = phi + 1", scalar_eq(phi**2, phi + 1))
    check("fusion matrix characteristic polynomial", scalar_eq(N_tau.charpoly().as_expr().subs({"lambda": phi}), 0))


if __name__ == "__main__":
    run()
