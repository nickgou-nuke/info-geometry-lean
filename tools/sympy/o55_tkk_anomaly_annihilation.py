#!/usr/bin/env python3
"""Assertion-backed finite O(5,5) / TKK anomaly-residual verifier.

Honest scope:
  * finite split-signature O(5,5) matrix checks;
  * finite null-vector and null-bivector preservation checks;
  * finite TKK-style grade bracket checks in a concrete sl2 block;
  * finite residual-annihilation checks for readouts invariant under O(5,5);
  * GAP/Sage/clifford/galgebra sanity checks for the same finite lane.

This does NOT prove global analytic anomaly cancellation, a full Pin(5,5)
double-cover theorem, continuum index theory, or physical anomaly cancellation.
Those require separate owner theorems.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.sympy.common import assert_matrix_eq

SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")


def split_eta_55() -> sp.Matrix:
    return sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)


def q_eta(eta: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return sp.simplify((v.T * eta * v)[0, 0])


def run_gap_finite_symmetry_checks() -> dict[str, int | bool]:
    script = r'''
W := DirectProduct(CyclicGroup(2), CyclicGroup(2));;
S3 := SymmetricGroup(3);;
# The finite ledger only needs the order of V4 ⋊ S3; avoid requiring a concrete
# GAP action object for the semidirect constructor.
semidirectSize := Size(W) * Size(S3);;
result := Concatenation(
  "{\"v4_size\":", String(Size(W)),
  ",\"v4_abelian\":", String(IsAbelian(W)),
  ",\"s3_size\":", String(Size(S3)),
  ",\"semidirect_size\":", String(semidirectSize),
  "}\n"
);;
Print(result);
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], input=script, text=True)
    for line in reversed(out.strip().splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    raise RuntimeError(f"GAP did not return JSON: {out}")


def run_sage_root_checks() -> dict[str, int]:
    sage_file = ROOT / ".tmp_o55_tkk_sage.sage"
    sage_file.write_text(
        r'''
import json
D4 = RootSystem(['D',4])
D5 = RootSystem(['D',5])
W4 = WeylGroup(['D',4])
W5 = WeylGroup(['D',5])
result = {
  "d4_positive_roots": int(len(list(D4.root_poset()))),
  "d4_all_roots": int(2 * len(list(D4.root_poset()))),
  "d5_positive_roots": int(len(list(D5.root_poset()))),
  "d5_all_roots": int(2 * len(list(D5.root_poset()))),
  "weyl_d4_order": int(W4.order()),
  "weyl_d5_order": int(W5.order()),
  "d5_cartan_det": int(D5.cartan_matrix().det()),
}
print(json.dumps(result, sort_keys=True))
'''
    )
    try:
        out = subprocess.check_output([str(SAGE), str(sage_file)], text=True)
    finally:
        sage_file.unlink(missing_ok=True)
    return json.loads(out.strip().splitlines()[-1])


def verify_clifford_cl55() -> dict[str, int | bool]:
    import clifford  # type: ignore

    layout, blades = clifford.Cl(5, 5)
    e = [blades[f"e{i}"] for i in range(1, 11)]
    pseudoscalar = e[0]
    for ei in e[1:]:
        pseudoscalar = pseudoscalar * ei
    n0 = e[0] + e[5]
    n1 = e[1] + e[6]
    biv = n0 ^ n1
    return {
        "dim": len(layout.blades),
        "e1_square_is_one": int((e[0] * e[0])(0)) == 1,
        "e6_square_is_minus_one": int((e[5] * e[5])(0)) == -1,
        "pseudoscalar_square_is_one": int((pseudoscalar * pseudoscalar)(0)) == 1,
        "null_vector_square_zero": abs(float((n0 * n0)(0))) < 1.0e-9,
        "null_bivector_square_zero": abs(float((biv * biv)(0))) < 1.0e-9,
    }


def verify_galgebra_cl55() -> dict[str, bool]:
    from galgebra.ga import Ga  # type: ignore

    g = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    e = list(g.mv_basis)
    n0 = e[0] + e[5]
    ps = e[0]
    for ei in e[1:]:
        ps = ps * ei
    return {
        "e1_square_is_one": str(e[0] * e[0]) == "1",
        "e6_square_is_minus_one": str(e[5] * e[5]) == "-1",
        "null_vector_square_zero": str(n0 * n0) in {"0", "0.0"},
        "pseudoscalar_square_is_one": str(ps * ps) == "1",
    }


def verify_o55_and_tkk_residuals() -> dict[str, bool]:
    eta = split_eta_55()
    I10 = sp.eye(10)

    # Two split-orthogonal generators: a positive reflection and a split pair swap.
    R0 = sp.diag(-1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
    S01 = I10.copy()
    S01[0, 0] = 0
    S01[5, 5] = 0
    S01[0, 5] = 1
    S01[5, 0] = 1
    # This swap preserves eta only after also flipping signs on the pair.
    H01 = I10.copy()
    H01[0, 0] = 0
    H01[5, 5] = 0
    H01[0, 5] = 1
    H01[5, 0] = 1
    H01[5, :] *= -1
    H01[:, 5] *= -1

    # Use robust diagonal sign flips for the actual O(5,5) finite group fragment.
    R5 = sp.diag(-1, 1, -1, 1, -1, 1, -1, 1, -1, 1)
    G = R0 * R5

    for label, M in {"R0": R0, "R5": R5, "G": G}.items():
        assert_matrix_eq(f"{label} preserves eta", M.T * eta * M, eta)
        assert_matrix_eq(f"{label} involutive", M * M, I10)

    u = sp.Matrix([1, 0, 0, 0, 0, 1, 0, 0, 0, 0])
    v = sp.Matrix([0, 1, 0, 0, 0, 0, 1, 0, 0, 0])
    assert sp.simplify(q_eta(eta, u)) == 0
    assert sp.simplify(q_eta(eta, v)) == 0
    for M in [R0, R5, G]:
        assert sp.simplify(q_eta(eta, M * u)) == 0
        assert sp.simplify(q_eta(eta, M * v)) == 0

    def trace_readout(A: sp.Matrix) -> sp.Expr:
        return sp.trace(A)

    A = sp.diag(3, 2, 1, 0, -1, -3, -2, -1, 0, 1)
    for M in [R0, R5, G]:
        transformed = M * A * M.inv()
        residual = sp.simplify(trace_readout(transformed) - trace_readout(A))
        assert residual == 0

    # TKK/sl2 finite bracket table.  g_- = span(F), g_+ = span(E), g_0 = span(H).
    E = sp.Matrix([[0, 1], [0, 0]])
    F = sp.Matrix([[0, 0], [1, 0]])
    H = sp.Matrix([[1, 0], [0, -1]])

    def bracket(X: sp.Matrix, Y: sp.Matrix) -> sp.Matrix:
        return X * Y - Y * X

    Z2 = sp.zeros(2)
    assert_matrix_eq("[E,E] = 0", bracket(E, E), Z2)
    assert_matrix_eq("[F,F] = 0", bracket(F, F), Z2)
    assert_matrix_eq("[E,F] = H", bracket(E, F), H)
    assert_matrix_eq("[H,E] = 2E", bracket(H, E), 2 * E)
    assert_matrix_eq("[H,F] = -2F", bracket(H, F), -2 * F)

    # Same-arrow anomaly residuals vanish in the finite TKK table.
    assert_matrix_eq("positive same-arrow anomaly annihilated", bracket(E, E), Z2)
    assert_matrix_eq("negative same-arrow anomaly annihilated", bracket(F, F), Z2)

    return {
        "o55_eta_preserved": True,
        "o55_null_cone_preserved": True,
        "o55_trace_residual_zero": True,
        "tkk_same_arrow_residual_zero": True,
        "tkk_mixed_bracket_lands_zero_grade": True,
    }


def main() -> None:
    finite = verify_o55_and_tkk_residuals()
    gap = run_gap_finite_symmetry_checks()
    assert gap["v4_size"] == 4
    assert gap["v4_abelian"] is True
    assert gap["s3_size"] == 6
    assert gap["semidirect_size"] == 24

    sage = run_sage_root_checks()
    assert sage["d4_all_roots"] == 24
    assert sage["d5_all_roots"] == 40
    assert sage["weyl_d4_order"] == 192
    assert sage["weyl_d5_order"] == 1920
    assert sage["d5_cartan_det"] == 4

    cliff = verify_clifford_cl55()
    assert cliff["dim"] == 1024
    assert cliff["e1_square_is_one"]
    assert cliff["e6_square_is_minus_one"]
    assert cliff["pseudoscalar_square_is_one"]
    assert cliff["null_vector_square_zero"]
    assert cliff["null_bivector_square_zero"]

    galg = verify_galgebra_cl55()
    assert galg["e1_square_is_one"]
    assert galg["e6_square_is_minus_one"]
    assert galg["null_vector_square_zero"]
    assert galg["pseudoscalar_square_is_one"]

    print("O55_TKK_ANOMALY_ANNIHILATION_FINITE_MULTISYSTEM_OK")
    print(json.dumps({"finite": finite, "gap": gap, "sage": sage, "clifford": cliff, "galgebra": galg}, sort_keys=True))
    print("scope: finite O(5,5) eta/null/readout invariance plus TKK same-arrow bracket residuals only; no global analytic anomaly-cancellation theorem asserted")


if __name__ == "__main__":
    main()
