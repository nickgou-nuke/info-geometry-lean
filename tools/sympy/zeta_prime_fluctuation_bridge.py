#!/usr/bin/env python3
"""Symbolic bridge from centered zeta zeros to prime-wave envelopes.

This verifies the algebra behind

  x^(1/2 + u + i v) = sqrt(x) * x^u * exp(i v log x).

The critical-line condition `u = 0` removes the scale-normal envelope `x^u`,
leaving a square-root envelope times a pure phase.  This is only the symbolic
envelope algebra of the explicit-formula fluctuation term, not a proof of RH or
of the explicit formula.
"""

from __future__ import annotations

import sympy as sp


x = sp.symbols("x", positive=True)
u, v = sp.symbols("u v", real=True)
I = sp.I


def same(a: sp.Expr, b: sp.Expr) -> bool:
    return sp.simplify(a - b) == 0


rho = sp.Rational(1, 2) + u + I * v
wave = x**rho
envelope = sp.sqrt(x) * x**u
phase = sp.exp(I * v * sp.log(x))
critical_wave = wave.subs(u, 0)


def main() -> None:
    assert same(wave.rewrite(sp.exp), (envelope * phase).rewrite(sp.exp))
    assert same(critical_wave.rewrite(sp.exp), (sp.sqrt(x) * phase).rewrite(sp.exp))

    critical_mirror = (-u, v)
    tangent_projector = (0, v)
    normal_projector = (u, 0)

    assert tangent_projector == (0, critical_mirror[1])
    assert normal_projector == (u, 0)
    assert normal_projector[0].subs(u, 0) == 0

    # Pairing u and -u under the critical mirror gives reciprocal scale factors.
    assert same((x**u * x**(-u)).rewrite(sp.exp), 1)

    print("zeta_prime_fluctuation_bridge: ok")
    print("  x^(1/2+u+iv) = sqrt(x) * x^u * exp(i*v*log(x))")
    print("  u=0 => square-root envelope with pure oscillatory phase")
    print("  J-normal projector P_J^- = (u, 0); RH-style packet sets u = 0")


if __name__ == "__main__":
    main()
