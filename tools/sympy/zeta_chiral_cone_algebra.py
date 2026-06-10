#!/usr/bin/env python3
"""Finite witness for zeta projector/chiral-cone algebra.

This mirrors `InfoGeometry.Canonical.ZetaChiralConeAlgebra`.

It checks only algebraic projector facts:

* antiunitary critical mirror `J F(u,v) = conjugate(F(-u,v))`;
* `P+ = (F + JF)/2`, `P- = (F - JF)/2`;
* a supplied J-even completed xi shadow has `P+ xi = xi`, `P- xi = 0`;
* an uncompleted zeta shadow can have nonzero odd/normal density.

No analytic zeta function, natural cone, AQFT algebra, Radon-Nikodym theorem,
or RH statement is proved here.
"""

from __future__ import annotations

import sympy as sp


u, v = sp.symbols("u v", real=True)


def conj_expr(expr: sp.Expr) -> sp.Expr:
    return sp.conjugate(expr)


def j_action(expr: sp.Expr) -> sp.Expr:
    return sp.simplify(conj_expr(expr.subs({u: -u})))


def p_plus(expr: sp.Expr) -> sp.Expr:
    return sp.simplify(sp.Rational(1, 2) * (expr + j_action(expr)))


def p_minus(expr: sp.Expr) -> sp.Expr:
    return sp.simplify(sp.Rational(1, 2) * (expr - j_action(expr)))


def assert_zero(expr: sp.Expr, label: str) -> None:
    if sp.simplify(expr) != 0:
        raise AssertionError((label, sp.factor(expr)))


def main() -> None:
    # A J-even completed-xi shadow: even in u and real-valued.
    xi = u**2 + v**2 + 1

    # An uncompleted-zeta shadow with a deliberately nonzero odd component.
    zeta = xi + u

    assert_zero(j_action(j_action(zeta)) - zeta, "J involutive")
    assert_zero(p_plus(zeta) + p_minus(zeta) - zeta, "projectors resolve")

    assert_zero(j_action(xi) - xi, "xi J-even premise")
    assert_zero(p_plus(xi) - xi, "P+ xi = xi")
    assert_zero(p_minus(xi), "P- xi = 0")

    odd_density = p_minus(zeta)
    assert_zero(odd_density - u, "uncompleted odd density")
    assert sp.simplify(odd_density.subs({u: 1, v: 0})) != 0

    # The odd density is J-odd.
    assert_zero(j_action(odd_density) + odd_density, "odd density J-odd")

    # Predicate-level chiral cone witness: encode cone membership as a supplied
    # boolean/assumption, not as an analytic theorem.
    xi_in_natural_cone = True
    xi_is_anchor = xi_in_natural_cone and sp.simplify(j_action(xi) - xi) == 0
    assert xi_is_anchor

    print("zeta_chiral_cone_algebra: ok")
    print("  J_action: F(u,v) -> conjugate(F(-u,v))")
    print("  completed_xi_shadow: P+ xi = xi and P- xi = 0")
    print("  uncompleted_zeta_shadow: P- zeta is a nonzero odd density")
    print("  chiral_cone_anchor: predicate-level cone membership plus J-evenness")


if __name__ == "__main__":
    main()

