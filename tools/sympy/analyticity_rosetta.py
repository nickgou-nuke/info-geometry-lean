#!/usr/bin/env python3
"""
Computational witnesses for the complex-analyticity Rosetta stone.

This script checks finite symbolic examples of the Cauchy--Riemann equations,
harmonic real/imaginary parts, and conformal Jacobian shape.  It is not a proof
of analyticity; the Lean bridge theorems in
`lean/InfoGeometry/Canonical/ComplexAnalyticBridge.lean` are the formal source.
"""

from __future__ import annotations

from dataclasses import dataclass
import sympy as sp

x, y = sp.symbols("x y", real=True)


@dataclass(frozen=True)
class AnalyticWitness:
    name: str
    u: sp.Expr
    v: sp.Expr

    @property
    def f_pair(self) -> tuple[sp.Expr, sp.Expr]:
        return (self.u, self.v)


def cr_residuals(u: sp.Expr, v: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    """Return residuals for u_x = v_y and u_y = -v_x."""
    return (
        sp.simplify(sp.diff(u, x) - sp.diff(v, y)),
        sp.simplify(sp.diff(u, y) + sp.diff(v, x)),
    )


def laplacian(expr: sp.Expr) -> sp.Expr:
    return sp.simplify(sp.diff(expr, x, 2) + sp.diff(expr, y, 2))


def jacobian(u: sp.Expr, v: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[sp.diff(u, x), sp.diff(u, y)], [sp.diff(v, x), sp.diff(v, y)]])


def conformal_residuals(u: sp.Expr, v: sp.Expr) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """
    For J = [[a,b],[c,d]], conformal holomorphic form is [[a,-c],[c,a]].
    Residuals: a-d, b+c, determinant-minus-scale^2.
    """
    J = jacobian(u, v)
    a, b, c, d = J[0, 0], J[0, 1], J[1, 0], J[1, 1]
    return (sp.simplify(a - d), sp.simplify(b + c), sp.simplify(J.det() - (a**2 + c**2)))


def report(w: AnalyticWitness) -> None:
    u, v = w.f_pair
    print(f"\n== {w.name} ==")
    print(f"u = {sp.simplify(u)}")
    print(f"v = {sp.simplify(v)}")
    print("CR residuals:", cr_residuals(u, v))
    print("Laplacian(u), Laplacian(v):", laplacian(u), laplacian(v))
    print("Jacobian:")
    sp.print_latex(jacobian(u, v))
    print(jacobian(u, v))
    print("Conformal residuals:", conformal_residuals(u, v))


def main() -> None:
    examples = [
        AnalyticWitness("z^2", x**2 - y**2, 2 * x * y),
        AnalyticWitness("z^3", x**3 - 3 * x * y**2, 3 * x**2 * y - y**3),
        AnalyticWitness("exp(z)", sp.exp(x) * sp.cos(y), sp.exp(x) * sp.sin(y)),
        AnalyticWitness("non-holomorphic conjugate(z)", x, -y),
        AnalyticWitness("non-holomorphic |z|^2", x**2 + y**2, 0),
    ]
    for w in examples:
        report(w)


if __name__ == "__main__":
    main()
