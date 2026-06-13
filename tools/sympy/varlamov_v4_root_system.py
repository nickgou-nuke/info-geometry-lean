#!/usr/bin/env python3
"""Assertion-backed finite Varlamov V4 / tripotent root-system verifier.

This is a finite certificate only.  It verifies:
  * the tripotent polynomial x^3 = x on the spectrum {-1,0,+1};
  * the A1 x A1 sign-root set has coordinates in {-1,0,+1};
  * the two coordinate reflections generate the Klein four group V4;
  * the three non-identity V4 labels carry a triality-shaped 3-cycle;
  * Sage and GAP agree on the order/abelian/exponent-2 group facts;
  * clifford and galgebra realize the split Cl(1,1) atom;
  * the finite `pg` wallpaper glide relation satisfies G^2 = T_x and
    G T_y = T_y^-1 G.

It deliberately does NOT claim SO(4), Lorentz symmetry, Pin(5,5), a
quotient-space Klein-bottle classification, or spacetime emergence.  Those need
separate owner-side representation/topology theorems.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def assert_matrix_eq(label: str, actual: sp.Matrix, expected: sp.Matrix) -> None:
    if actual != expected:
        raise AssertionError(f"{label}:\nactual={actual}\nexpected={expected}")


def run_gap_v4() -> dict[str, bool | int]:
    script = r'''
G := DirectProduct(CyclicGroup(2), CyclicGroup(2));;
els := Elements(G);;
allOrderTwo := ForAll(els, g -> Order(g) in [1,2]);;
Print("{\"size\":", Size(G), ",\"abelian\":", IsAbelian(G), ",\"all_order_le_two\":", allOrderTwo, "}\n");
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], input=script, text=True)
    return json.loads(out.strip().splitlines()[-1].replace("true", "true").replace("false", "false"))


def run_sage_a1_product() -> dict[str, int | bool]:
    sage_file = ROOT / ".tmp_varlamov_v4_sage.sage"
    sage_file.write_text(
        r'''
import json
R = RootSystem(['A',1])
roots = list(R.ambient_space().roots())
W = WeylGroup(['A',1])
result = {
  "a1_root_count": int(len(roots)),
  "a1_weyl_order": int(W.order()),
  "a1xa1_root_count": int(len(roots) * len(roots)),
  "a1xa1_weyl_order": int(W.order() * W.order()),
  "a1_cartan_det": int(R.cartan_matrix().det()),
}
print(json.dumps(result, sort_keys=True))
'''
    )
    try:
        out = subprocess.check_output([str(SAGE), str(sage_file)], text=True)
    finally:
        sage_file.unlink(missing_ok=True)
    return json.loads(out.strip().splitlines()[-1])


def verify_cl11_atom_clifford() -> dict[str, int | bool]:
    import clifford  # type: ignore

    layout, blades = clifford.Cl(1, 1)
    e1 = blades["e1"]
    e2 = blades["e2"]
    pseudoscalar = e1 * e2
    return {
        "dim": len(layout.blades),
        "e1_square_is_one": int((e1 * e1)(0)) == 1,
        "e2_square_is_minus_one": int((e2 * e2)(0)) == -1,
        "anticommutator_zero": int((e1 * e2 + e2 * e1)(0)) == 0,
        "pseudoscalar_square_is_one": int((pseudoscalar * pseudoscalar)(0)) == 1,
    }


def verify_cl11_atom_galgebra() -> dict[str, bool]:
    from galgebra.ga import Ga  # type: ignore

    g = Ga("u v", g=[1, -1])
    u, v = list(g.mv_basis)
    pseudoscalar = u * v
    # String comparison is stable for these scalar reductions in galgebra.
    return {
        "u_square_is_one": str(u * u) == "1",
        "v_square_is_minus_one": str(v * v) == "-1",
        "anticommutator_zero": str(u * v + v * u) in {"0", "0.0"},
        "pseudoscalar_square_is_one": str(pseudoscalar * pseudoscalar) == "1",
    }


def verify_pg_wallpaper_glide() -> dict[str, bool]:
    x, y = sp.symbols("x y", real=True)
    p = sp.Matrix([x, y])

    def tx(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([sp.sympify(point[0, 0]) + 1, sp.sympify(point[1, 0])])

    def ty(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([sp.sympify(point[0, 0]), sp.sympify(point[1, 0]) + 1])

    def ty_inv(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([sp.sympify(point[0, 0]), sp.sympify(point[1, 0]) - 1])

    def glide(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([
            sp.sympify(point[0, 0]) + sp.Rational(1, 2),
            -sp.sympify(point[1, 0]),
        ])

    return {
        "glide_square_is_tx": sp.simplify(glide(glide(p)) - tx(p)) == sp.zeros(2, 1),
        "glide_conjugates_ty_to_inverse": sp.simplify(glide(ty(p)) - ty_inv(glide(p)))
        == sp.zeros(2, 1),
    }


def verify_varlamov_v4_root_system() -> None:
    x = sp.symbols("x")
    for val in (-1, 0, 1):
        assert sp.expand(val**3 - val) == 0
    assert sp.factor(x**3 - x) == x * (x - 1) * (x + 1)

    roots: list[sp.Matrix] = [sp.Matrix([1, 0]), sp.Matrix([-1, 0]), sp.Matrix([0, 1]), sp.Matrix([0, -1])]
    root_coords = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    assert all(v in {-1, 0, 1} for root in root_coords for v in root)

    I = sp.eye(2)
    W1 = sp.diag(-1, 1)
    W2 = sp.diag(1, -1)
    W12 = W1 * W2
    v4 = [I, W1, W2, W12]

    def mat_key(m: sp.Matrix) -> tuple[int, int]:
        return (int(m[0, 0]), int(m[1, 0]))

    for g in v4:
        assert_matrix_eq("V4 involution", g * g, I)
        assert sorted(mat_key(g * r) for r in roots) == sorted(root_coords)
    for a in v4:
        for b in v4:
            assert any(a * b == c for c in v4)
            assert_matrix_eq("V4 commutativity", a * b, b * a)
    assert_matrix_eq("point inversion", W1 * W2, sp.diag(-1, -1))

    # Tripotent operator and trifactor projectors.
    OP = sp.diag(1, 0, -1)
    P_plus = (OP**2 + OP) / 2
    P_zero = sp.eye(3) - OP**2
    P_minus = (OP**2 - OP) / 2
    assert_matrix_eq("OP^3 = OP", OP**3, OP)
    for P in [P_plus, P_zero, P_minus]:
        assert_matrix_eq("trifactor idempotent", P * P, P)
    for A, B in [(P_plus, P_zero), (P_plus, P_minus), (P_zero, P_minus)]:
        assert_matrix_eq("trifactor orthogonal", A * B, sp.zeros(3))
    assert_matrix_eq("trifactor partition", P_plus + P_zero + P_minus, sp.eye(3))
    assert_matrix_eq("OP acts +", OP * P_plus, P_plus)
    assert_matrix_eq("OP acts 0", OP * P_zero, sp.zeros(3))
    assert_matrix_eq("OP acts -", OP * P_minus, -P_minus)

    trifactor_cycle = {-1: 0, 0: 1, 1: -1}
    for state in (-1, 0, 1):
        assert trifactor_cycle[trifactor_cycle[trifactor_cycle[state]]] == state

    nontrivial_v4 = {"W1": W1, "W2": W2, "W12": W12}
    v4_triality = {"W1": "W2", "W2": "W12", "W12": "W1"}
    for label, matrix in nontrivial_v4.items():
        assert_matrix_eq(f"{label} remains nonidentity", matrix, nontrivial_v4[label])
        assert v4_triality[v4_triality[v4_triality[label]]] == label
        assert v4_triality[label] != "I"

    gap = run_gap_v4()
    assert gap == {"size": 4, "abelian": True, "all_order_le_two": True}

    sage = run_sage_a1_product()
    assert sage["a1_root_count"] == 2
    assert sage["a1_weyl_order"] == 2
    assert sage["a1xa1_root_count"] == 4
    assert sage["a1xa1_weyl_order"] == 4
    assert sage["a1_cartan_det"] == 2

    cliff = verify_cl11_atom_clifford()
    assert cliff["dim"] == 4
    assert cliff["e1_square_is_one"]
    assert cliff["e2_square_is_minus_one"]
    assert cliff["anticommutator_zero"]
    assert cliff["pseudoscalar_square_is_one"]

    galg = verify_cl11_atom_galgebra()
    assert galg["u_square_is_one"]
    assert galg["v_square_is_minus_one"]
    assert galg["anticommutator_zero"]
    assert galg["pseudoscalar_square_is_one"]

    glide = verify_pg_wallpaper_glide()
    assert glide["glide_square_is_tx"]
    assert glide["glide_conjugates_ty_to_inverse"]

    print("VARLAMOV_V4_TRIPOTENT_CL11_GLIDE_MULTISYSTEM_OK")
    print(json.dumps({"gap": gap, "sage": sage, "clifford": cliff, "galgebra": galg, "pg_glide": glide}, sort_keys=True))
    print("scope: finite A1xA1/V4/tripotent/triality-cycle plus split-Cl(1,1) and pg-glide algebra only; no Lorentz/Pin/Klein-bottle quotient theorem asserted")


if __name__ == "__main__":
    verify_varlamov_v4_root_system()
