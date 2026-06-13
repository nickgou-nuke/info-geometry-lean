#!/usr/bin/env python3
"""Signed-permutation split-octonion automorphism verifier.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionSignedPermutationAutomorphism.lean

Scope: concrete orientation-preserving signed-permutation automorphism witnesses
for the explicit Zorn split-octonion multiplication table.  These are genuine
finite automorphisms of the formalized algebra, not a classification theorem for
`Aut(O_s) = G2(2)`.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
MULT_PATH = ROOT / "tools" / "sympy" / "split_octonion_multiplication.py"
spec = importlib.util.spec_from_file_location("split_octonion_multiplication", MULT_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {MULT_PATH}")
mult = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mult
spec.loader.exec_module(mult)

import sympy as sp

Zorn = mult.Zorn


def assert_eq(lhs, rhs, msg: str) -> None:
    if isinstance(lhs, Zorn):
        ok = lhs == rhs
    else:
        ok = sp.simplify(lhs - rhs) == 0
    if not ok:
        raise AssertionError(f"{msg}: {lhs!r} != {rhs!r}")


def symbolic_element(prefix: str) -> Zorn:
    a, b = sp.symbols(f"{prefix}a {prefix}b")
    x0, x1, x2 = sp.symbols(f"{prefix}x0 {prefix}x1 {prefix}x2")
    y0, y1, y2 = sp.symbols(f"{prefix}y0 {prefix}y1 {prefix}y2")
    return Zorn(a, b, (x0, x1, x2), (y0, y1, y2))


def rho(z: Zorn) -> Zorn:
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x2, x0, x1), (y2, y0, y1))


def tau(z: Zorn) -> Zorn:
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x0, -x1, -x2), (y0, -y1, -y2))


def sigma(z: Zorn) -> Zorn:
    """Orientation-preserving signed transposition: (0 1) plus a sign on coordinate 2."""
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x1, x0, -x2), (y1, y0, -y2))


def compose(f, g):
    return lambda z: f(g(z))


def verify_automorphism(name: str, phi) -> None:
    X = symbolic_element("X")
    Y = symbolic_element("Y")
    assert_eq(phi(X * Y), phi(X) * phi(Y), f"{name}_mul")
    assert_eq(phi(X).det(), X.det(), f"{name}_det")
    assert_eq(phi(mult.EPLUS), mult.EPLUS, f"{name}_eplus")
    assert_eq(phi(mult.EMINUS), mult.EMINUS, f"{name}_eminus")


def main() -> None:
    X = symbolic_element("X")
    for name, phi in [("rho", rho), ("tau", tau), ("sigma", sigma), ("rho_sigma", compose(rho, sigma)), ("sigma_tau", compose(sigma, tau))]:
        verify_automorphism(name, phi)

    assert_eq(rho(rho(rho(X))), X, "rho_order_three")
    assert_eq(tau(tau(X)), X, "tau_order_two")
    assert_eq(sigma(sigma(X)), X, "sigma_order_two")

    assert_eq(sigma(mult.UP[0]), mult.UP[1], "sigma_up0")
    assert_eq(sigma(mult.UP[1]), mult.UP[0], "sigma_up1")
    assert_eq(sigma(mult.UP[2]), Zorn(0, 0, (0, 0, -1), (0, 0, 0)), "sigma_up2")
    assert_eq(sigma(mult.DOWN[0]), mult.DOWN[1], "sigma_down0")
    assert_eq(sigma(mult.DOWN[1]), mult.DOWN[0], "sigma_down1")
    assert_eq(sigma(mult.DOWN[2]), Zorn(0, 0, (0, 0, 0), (0, 0, -1)), "sigma_down2")

    print("OK split_octonion_signed_permutation_automorphisms: rho, tau, sigma and composites preserve multiplication and detZ")
    print("OK orders: rho^3=id, tau^2=id, sigma^2=id")
    print("scope: concrete orientation-preserving signed-permutation automorphism witnesses; no full Aut(O_s)=G2(2) classification claimed")


if __name__ == "__main__":
    main()
