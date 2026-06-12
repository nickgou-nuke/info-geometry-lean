"""Finite quadratic Legendre-transform mirror.

This mirrors `InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite`.

Closed scope:
* flat `R^4` quadratic kinetic energy `T(v)=1/2 v·v`;
* Lagrangian `L(q,v)=T(v)-V(q)`;
* canonical momentum `p=v`;
* Legendre readout `p·v-L(q,v)=H(q,p)=T(p)+V(q)`;
* nonnegative sample potential gives nonnegative Hamiltonian.

No differentiable tangent bundle, Euler-Lagrange equations, Hamiltonian flow,
Noether theorem, partition function, or field dynamics are claimed here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    simplified = sp.simplify(expr)
    if simplified != 0:
        raise AssertionError(f"{label} did not simplify to zero:\n{simplified}")


def main() -> None:
    v = sp.Matrix(sp.symbols("v0 v1 v2 v3"))
    q = sp.Matrix(sp.symbols("q0 q1 q2 q3"))
    potential = sp.symbols("Vq", real=True)

    kinetic_v = sp.Rational(1, 2) * (v.dot(v))
    lagrangian = kinetic_v - potential
    conjugate_momentum = v
    hamiltonian = sp.Rational(1, 2) * conjugate_momentum.dot(conjugate_momentum) + potential
    legendre_readout = conjugate_momentum.dot(v) - lagrangian

    assert_zero(legendre_readout - hamiltonian, "Legendre readout equals Hamiltonian")
    assert_zero(hamiltonian - (kinetic_v + potential), "Hamiltonian total energy")

    nonnegative_potential = q.dot(q)
    p = sp.Matrix(sp.symbols("p0 p1 p2 p3"))
    h_nonnegative = sp.Rational(1, 2) * p.dot(p) + nonnegative_potential
    expected_sum_of_squares = (
        sp.Rational(1, 2) * sum(pi**2 for pi in p) + sum(qi**2 for qi in q)
    )
    assert_zero(h_nonnegative - expected_sum_of_squares, "nonnegative Hamiltonian sample")

    print("biquaternion_kahler_legendre_finite: ok")
    print("  quadratic Legendre readout equals kinetic-plus-potential Hamiltonian")
    print("  nonnegative potential sample rewrites as a sum of squares")
    print("  honest scope: finite flat R^4 algebra only")


if __name__ == "__main__":
    main()
