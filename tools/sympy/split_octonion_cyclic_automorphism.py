#!/usr/bin/env python3
"""Concrete split-octonion cyclic automorphism verifier.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionCyclicAutomorphism.lean

Scope: one exact order-three automorphism of the explicit Zorn split-octonion
multiplication surface.  This is a kernel-friendly G2(2)-type automorphism
witness, not a proof that the full automorphism group is G2(2).
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


def rho(z: Zorn) -> Zorn:
    """Cyclically rotate vector coordinates 0 -> 1 -> 2 -> 0.

    In tuple form this sends (x0,x1,x2) to (x2,x0,x1), so basis e0 maps to e1,
    e1 maps to e2, and e2 maps to e0.  It applies the same orientation-preserving
    rotation to upper and lower vectors and fixes the two diagonal idempotents.
    """
    x0, x1, x2 = z.x
    y0, y1, y2 = z.y
    return Zorn(z.a, z.b, (x2, x0, x1), (y2, y0, y1))


def assert_eq(lhs, rhs, msg: str) -> None:
    if isinstance(lhs, Zorn):
        ok = lhs == rhs
    else:
        ok = sp.simplify(lhs - rhs) == 0
    if not ok:
        raise AssertionError(f"{msg}: {lhs!r} != {rhs!r}")


def symbolic_element(prefix: str) -> Zorn:
    a, b, x0, x1, x2, y0, y1, y2 = sp.symbols(f"{prefix}a {prefix}b {prefix}x0 {prefix}x1 {prefix}x2 {prefix}y0 {prefix}y1 {prefix}y2")
    return Zorn(a, b, (x0, x1, x2), (y0, y1, y2))


def main() -> None:
    X = symbolic_element("X")
    Y = symbolic_element("Y")

    # Automorphism law: rho(XY) = rho(X)rho(Y).
    assert_eq(rho(X * Y), rho(X) * rho(Y), "rho_mul")

    # Norm preservation follows symbolically, but verify it directly too.
    assert_eq(rho(X).det(), X.det(), "rho_det")

    # Order three and diagonal fixed points.
    assert_eq(rho(rho(rho(X))), X, "rho_order_three")
    assert_eq(rho(mult.EPLUS), mult.EPLUS, "rho_e_plus")
    assert_eq(rho(mult.EMINUS), mult.EMINUS, "rho_e_minus")

    # Explicit 1+3 slot cycle.
    assert_eq(rho(mult.UP[0]), mult.UP[1], "rho_up0")
    assert_eq(rho(mult.UP[1]), mult.UP[2], "rho_up1")
    assert_eq(rho(mult.UP[2]), mult.UP[0], "rho_up2")
    assert_eq(rho(mult.DOWN[0]), mult.DOWN[1], "rho_down0")
    assert_eq(rho(mult.DOWN[1]), mult.DOWN[2], "rho_down1")
    assert_eq(rho(mult.DOWN[2]), mult.DOWN[0], "rho_down2")

    # A concrete product-table sanity check transported by rho.
    assert_eq(rho(mult.UP[0] * mult.UP[1]), rho(mult.UP[0]) * rho(mult.UP[1]), "rho_basis_product")

    print("OK split_octonion_cyclic_automorphism: rho^3=id, rho(XY)=rho(X)rho(Y), det rho(X)=det X")
    print("scope: one concrete order-three split-octonion automorphism; no full Aut(O_s)=G2(2) group-classification theorem claimed")


if __name__ == "__main__":
    main()
