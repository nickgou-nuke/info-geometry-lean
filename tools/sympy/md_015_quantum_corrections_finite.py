#!/usr/bin/env python3
"""Finite witness for MD 015 quantum-correction algebra.

Mirrors `InfoGeometry.Physics.MD015QuantumCorrectionsFinite`.

The requested upstream `015.md` is absent at the fetched MD revision; the closest
available source is `n015.md`.  Verified theorem-safe content only:
* formal three-loop scalar effective-action polynomial;
* scalar one-loop trace-log slot additivity;
* quadratic stationary fluctuation expansion;
* scalar FRG/Wetterich right-hand-side additivity;
* finite quaternion condensate fluctuation norm expansion.

No path integral, functional determinant, renormalizability theorem, exact RG
equation, asymptotic-safety claim, Hawking-radiation correction, or black-hole
information theorem is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def qadd(p, q):
    return tuple(pi + qi for pi, qi in zip(p, q))


def qnorm_sq(q):
    return sum(x * x for x in q)


def qdot(p, q):
    return sum(pi * qi for pi, qi in zip(p, q))


def main() -> int:
    print("=" * 72)
    print("MD 015 FINITE QUANTUM-CORRECTION ALGEBRA")
    print("=" * 72)

    hbar, S, G1, G2, G3 = sp.symbols("hbar S G1 G2 G3")
    gamma2 = S + hbar * G1 + hbar**2 * G2
    gamma3 = gamma2 + hbar**3 * G3
    assert_zero(gamma3 - (gamma2 + hbar**3 * G3), "three-loop extends two-loop")
    assert_zero(gamma3.subs(hbar, 0) - S, "three-loop classical limit")
    assert_zero(gamma3 - S - (hbar * G1 + hbar**2 * G2 + hbar**3 * G3), "three-loop remainder")
    print("formal loop-polynomial identities: OK")

    T, U = sp.symbols("T U")
    I = sp.I
    one_loop = lambda X: I / 2 * X
    assert_zero(one_loop(T + U) - (one_loop(T) + one_loop(U)), "one-loop trace-log slot additivity")
    assert_zero(one_loop(0), "one-loop trace-log zero")
    print("one-loop scalar trace-log slot: OK")

    S0, L, H, delta = sp.symbols("S0 L H delta")
    quad = S0 + L * delta + sp.Rational(1, 2) * H * delta**2
    stationary_quad = quad.subs(L, 0)
    assert_zero(stationary_quad - S0 - sp.Rational(1, 2) * H * delta**2, "stationary quadratic remainder")
    assert_zero(stationary_quad.subs(delta, -delta) - stationary_quad, "stationary quadratic evenness")
    print("quadratic fluctuation action identities: OK")

    Kinv, dR, dS = sp.symbols("Kinv dR dS")
    frg = lambda d: sp.Rational(1, 2) * Kinv * d
    assert_zero(frg(dR + dS) - (frg(dR) + frg(dS)), "FRG scalar RHS additivity")
    assert_zero(frg(0), "FRG scalar RHS zero cutoff derivative")
    print("finite FRG scalar shadow: OK")

    Q0 = sp.symbols("Q00 Q01 Q02 Q03")
    q = sp.symbols("q0 q1 q2 q3")
    assert_zero(
        qnorm_sq(qadd(Q0, q)) - (qnorm_sq(Q0) + 2 * qdot(Q0, q) + qnorm_sq(q)),
        "quaternion fluctuation norm expansion",
    )
    print("quaternion condensate fluctuation norm expansion: OK")

    print("=" * 72)
    print("MD 015 FINITE QUANTUM-CORRECTION ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
