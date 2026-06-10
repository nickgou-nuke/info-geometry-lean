#!/usr/bin/env python3
"""Completed-ξ projector bridge: SymPy shadow.

Mirrors the theorem-safe Lean bridge
`InfoGeometry.Arithmetic.CompletedXiProjectorBridge`.

We do NOT formalize the analytic completed ξ-function itself here. Instead we
verify the exact algebra already present in the Lean owner files:

- antiunitary critical reflection on `s = σ + iτ`:
    s ↦ 1 - conjugate(s)
- centered chart `(u, v) = (σ - 1/2, τ)`
- critical mirror `(u, v) ↦ (-u, v)`
- tangent projector `P⁺(u, v) = (0, v)`
- normal projector `P⁻(u, v) = (u, 0)`

For antiunitary fixed points (`σ = 1/2`) the tangent projector is the identity
and the normal projector vanishes.
"""

from __future__ import annotations

import sympy as sp

sigma, tau = sp.symbols("sigma tau", real=True)


def antiunitary_critical_reflection(sig: sp.Expr, t: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (1 - sig, t)


def centered_of_complex(sig: sp.Expr, t: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (sig - sp.Rational(1, 2), t)


def critical_mirror(u: sp.Expr, v: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (-u, v)


def critical_tangent_projector(u: sp.Expr, v: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (sp.Integer(0), v)


def critical_normal_projector(u: sp.Expr, v: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (u, sp.Integer(0))


def same_pair(a: tuple[sp.Expr, sp.Expr], b: tuple[sp.Expr, sp.Expr]) -> bool:
    return all(sp.simplify(x - y) == 0 for x, y in zip(a, b, strict=True))


def main() -> None:
    # Generic transport from complex antiunitary reflection to centered critical mirror.
    reflected = antiunitary_critical_reflection(sigma, tau)
    centered_reflected = centered_of_complex(*reflected)
    mirrored_centered = critical_mirror(*centered_of_complex(sigma, tau))
    assert same_pair(centered_reflected, mirrored_centered)

    # Fixed-point condition of the antiunitary reflection: sigma = 1/2.
    fixed_sigma = sp.solve(sp.Eq(antiunitary_critical_reflection(sigma, tau)[0], sigma), sigma)
    assert fixed_sigma == [sp.Rational(1, 2)]

    # Instantiate a symbolic antiunitary-fixed anchor point.
    anchor = centered_of_complex(sp.Rational(1, 2), tau)
    assert anchor == (sp.Integer(0), tau)

    tangent = critical_tangent_projector(*anchor)
    normal = critical_normal_projector(*anchor)

    assert same_pair(tangent, anchor)
    assert same_pair(normal, (sp.Integer(0), sp.Integer(0)))
    assert same_pair(critical_mirror(*anchor), anchor)

    print("completed_xi_projector_bridge: ok")
    print("  antiunitary fixed locus on complex chart: sigma = 1/2")
    print("  centered fixed locus: u = 0")
    print("  tangent projector on fixed anchor: P_plus(anchor) = anchor")
    print("  normal projector on fixed anchor: P_minus(anchor) = 0")


if __name__ == "__main__":
    main()
