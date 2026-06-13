#!/usr/bin/env python3
"""Signed-coordinate split-octonion automorphism verifier.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionG2TypeGenerators.lean

Scope: concrete orientation-preserving signed-coordinate automorphisms of the
explicit Zorn split-octonion product.  These are finite G2(2)-type generator
witnesses inside the split-octonion automorphism group, not a classification of
the full automorphism group as G2(2).
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
    a, b, x0, x1, x2, y0, y1, y2 = sp.symbols(
        f"{prefix}a {prefix}b {prefix}x0 {prefix}x1 {prefix}x2 {prefix}y0 {prefix}y1 {prefix}y2"
    )
    return Zorn(a, b, (x0, x1, x2), (y0, y1, y2))


def rho(z: Zorn) -> Zorn:
    """Cyclic rotation e0 -> e1 -> e2 -> e0 on both vector slots."""
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x2, x0, x1), (y2, y0, y1))


def tau(z: Zorn) -> Zorn:
    """Orientation-preserving sign flip diag(1,-1,-1) on both vector slots."""
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x0, -x1, -x2), (y0, -y1, -y2))


def verify_automorphism(name: str, phi) -> None:
    X = symbolic_element("X")
    Y = symbolic_element("Y")
    assert_eq(phi(X * Y), phi(X) * phi(Y), f"{name}_mul")
    assert_eq(phi(X).det(), X.det(), f"{name}_det")
    assert_eq(phi(mult.EPLUS), mult.EPLUS, f"{name}_eplus")
    assert_eq(phi(mult.EMINUS), mult.EMINUS, f"{name}_eminus")


def compose(f, g):
    return lambda z: f(g(z))


def main() -> None:
    verify_automorphism("tau", tau)

    X = symbolic_element("X")
    assert_eq(tau(tau(X)), X, "tau_order_two")
    assert_eq(tau(mult.UP[0]), mult.UP[0], "tau_up0")
    assert_eq(tau(mult.UP[1]), Zorn(0, 0, (0, -1, 0), (0, 0, 0)), "tau_up1")
    assert_eq(tau(mult.UP[2]), Zorn(0, 0, (0, 0, -1), (0, 0, 0)), "tau_up2")
    assert_eq(tau(mult.DOWN[0]), mult.DOWN[0], "tau_down0")
    assert_eq(tau(mult.DOWN[1]), Zorn(0, 0, (0, 0, 0), (0, -1, 0)), "tau_down1")
    assert_eq(tau(mult.DOWN[2]), Zorn(0, 0, (0, 0, 0), (0, 0, -1)), "tau_down2")

    # A composite of two verified automorphisms is also checked symbolically here.
    # This gives an additional nontrivial finite subgroup witness without claiming
    # a full G2(2) presentation.
    verify_automorphism("rho_after_tau", compose(rho, tau))

    print("OK split_octonion_signed_automorphisms: tau^2=id, tau(XY)=tau(X)tau(Y), det tau(X)=det X")
    print("OK composite rho∘tau also preserves multiplication and detZ")
    print("scope: concrete finite G2(2)-type automorphism generators; no full Aut(O_s)=G2(2) classification claimed")


if __name__ == "__main__":
    main()
