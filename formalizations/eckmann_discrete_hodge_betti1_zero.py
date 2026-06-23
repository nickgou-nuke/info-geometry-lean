#!/usr/bin/env python3
"""Finite Eckmann degree-1 Hodge witness.

The Lean theorem owns the proof.  This script checks the finite matrix model:
closed 1-cochains modulo exact 1-cochains have dimension b1, and when b1=0
the degree-1 Hodge Laplacian has zero-dimensional kernel.
"""

from __future__ import annotations

import os
from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class DegreeOneComplex:
    name: str
    d0: sp.Matrix
    d1: sp.Matrix

    @property
    def n1(self) -> int:
        return self.d0.rows

    def laplacian1(self) -> sp.Matrix:
        return self.d1.T * self.d1 + self.d0 * self.d0.T

    def betti1(self) -> int:
        return self.d1.cols - self.d1.rank() - self.d0.rank()

    def harmonic1_dim(self) -> int:
        return self.laplacian_kernel_dim()

    def laplacian_kernel_dim(self) -> int:
        L1 = self.laplacian1()
        return L1.cols - L1.rank()

    def energy_identity_residual(self) -> sp.Expr:
        xs = sp.symbols(f"x0:{self.n1}")
        x = sp.Matrix(xs)
        lap_energy = (x.T * self.laplacian1() * x)[0]
        closed_energy = (self.d1 * x).dot(self.d1 * x)
        coclosed_energy = (self.d0.T * x).dot(self.d0.T * x)
        return sp.expand(lap_energy - closed_energy - coclosed_energy)


def path_tree_complex() -> DegreeOneComplex:
    d0 = sp.Matrix([[-1, 1, 0], [0, -1, 1]])
    d1 = sp.zeros(0, 2)
    return DegreeOneComplex("path-tree", d0, d1)


def triangle_cycle_complex() -> DegreeOneComplex:
    d0 = sp.Matrix([[-1, 1, 0], [0, -1, 1], [1, 0, -1]])
    d1 = sp.zeros(0, 3)
    return DegreeOneComplex("triangle-cycle", d0, d1)


def check_complex(C: DegreeOneComplex, expected_b1: int) -> None:
    assert C.d1 * C.d0 == sp.zeros(C.d1.rows, C.d0.cols)
    b1 = C.betti1()
    harmonic_dim = C.laplacian_kernel_dim()
    assert b1 == expected_b1, (C.name, b1, expected_b1)
    assert harmonic_dim == expected_b1, (C.name, harmonic_dim, expected_b1)
    assert C.energy_identity_residual() == 0, C.name
    print(
        f"{C.name}: rank(d0)={C.d0.rank()} nullity(d1)={C.d1.cols - C.d1.rank()} "
        f"b1={b1} dim ker L1={harmonic_dim} energy=ok"
    )


def optional_backend_report() -> None:
    os.environ.setdefault("NUMBA_DISABLE_JIT", "1")
    try:
        from clifford import Cl  # type: ignore

        _, blades = Cl(2)
        e1 = blades["e1"]
        clifford_ok = bool((e1 * e1)[()] == 1)
    except Exception as exc:  # pragma: no cover - environment report
        clifford_ok = f"unavailable: {exc.__class__.__name__}: {exc}"

    try:
        from galgebra.ga import Ga  # type: ignore

        ga = Ga("e1 e2", g=[1, 1])
        e1, e2 = ga.mv()
        galgebra_ok = str(e1 ^ e2) != "0"
    except Exception as exc:  # pragma: no cover - environment report
        galgebra_ok = f"unavailable: {exc.__class__.__name__}: {exc}"

    print(f"clifford backend: {clifford_ok}")
    print(f"galgebra backend: {galgebra_ok}")


def main() -> None:
    check_complex(path_tree_complex(), expected_b1=0)
    check_complex(triangle_cycle_complex(), expected_b1=1)
    optional_backend_report()


if __name__ == "__main__":
    main()
