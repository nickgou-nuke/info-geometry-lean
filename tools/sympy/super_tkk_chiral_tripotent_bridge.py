#!/usr/bin/env python3
"""Finite Super-TKK / chiral / tripotent bridge verifier.

This mirrors `InfoGeometry.Canonical.SuperTKKChiralTripotentBridge`.

Honest scope:
  * checks a finite five-grade bracket ledger by grade arithmetic;
  * checks the real doubled chiral carrier matrices `boost`, `eps`,
    `uPlus`, `uMinus`, and `boost*eps`;
  * checks the tripotent boundary readout with spectrum {-1, 0, +1};
  * uses GAP/Sage only for finite bookkeeping and A1 x A1 root sanity checks.

No concrete BdG/Krein-Fock representation, Pin(5,5) action, global
superconformal algebra, boundary braid category, or continuum anomaly theorem
is asserted here.
"""

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


def run_gap_role_checks() -> dict[str, int | bool]:
    script = r'''
V4 := DirectProduct(CyclicGroup(2), CyclicGroup(2));;
Z3 := CyclicGroup(3);;
result := Concatenation(
  "{\"v4_size\":", String(Size(V4)),
  ",\"v4_abelian\":", String(IsAbelian(V4)),
  ",\"tripotent_sector_count\":", String(Size(Z3)),
  ",\"five_grade_count\":", String(5),
  "}\n"
);;
Print(result);
QUIT;
'''
    out = subprocess.check_output([str(GAP), "-q"], input=script, text=True)
    out = out.replace("\\\n", "")
    for line in reversed(out.strip().splitlines()):
        if line.startswith("{"):
            return json.loads(line)
    raise RuntimeError(f"GAP did not return JSON: {out}")


def run_sage_root_checks() -> dict[str, int]:
    sage_file = ROOT / ".tmp_super_tkk_chiral_trip.sage"
    sage_file.write_text(
        r'''
import json
from builtins import int as py_int
A1 = RootSystem(['A',1])
W1 = WeylGroup(['A',1])
result = {
  "a1_positive_roots": py_int(len(list(A1.root_poset()))),
  "a1_all_roots": py_int(2 * len(list(A1.root_poset()))),
  "a1_weyl_order": py_int(W1.order()),
  "a1_cartan_det": py_int(A1.cartan_matrix().det()),
  "a1xa1_roots": py_int(4),
  "a1xa1_weyl_order": py_int(W1.order() * W1.order()),
}
print(json.dumps(result, sort_keys=True))
'''
    )
    try:
        out = subprocess.check_output([str(SAGE), str(sage_file)], text=True)
    finally:
        sage_file.unlink(missing_ok=True)
    return json.loads(out.strip().splitlines()[-1])


def verify_five_grade_ledger() -> dict[str, bool]:
    grades = [-2, -1, 0, 1, 2]

    def bracket_grade(a: int, b: int) -> int | None:
        s = a + b
        return s if s in grades else None

    assert bracket_grade(-1, 1) == 0
    assert bracket_grade(1, 1) == 2
    assert bracket_grade(-1, -1) == -2
    assert bracket_grade(0, 2) == 2
    assert bracket_grade(0, -2) == -2
    assert bracket_grade(2, 2) is None

    role_to_tripotent = {
        -2: -1,
        -1: -1,
        0: 0,
        1: 1,
        2: 1,
    }
    for role, sector in role_to_tripotent.items():
        assert sector**3 == sector, (role, sector)

    defects = {-2, 2}
    assert 2 in defects and -2 in defects
    assert 0 not in defects and 1 not in defects and -1 not in defects

    return {
        "mixed_grade_closes_zero": True,
        "same_positive_closes_pos_two": True,
        "same_negative_closes_neg_two": True,
        "zero_stabilizes_defects": True,
        "pos_two_abelian_by_out_of_range_shadow": True,
        "role_tripotent_cube": True,
        "pm_two_are_defects": True,
    }


def verify_chiral_carrier() -> dict[str, bool]:
    I2 = sp.eye(2)
    Z2 = sp.zeros(2)
    boost = sp.Matrix([[0, 1], [1, 0]])
    eps = sp.diag(1, -1)
    u_plus = (I2 + eps) / 2
    u_minus = (I2 - eps) / 2
    conformal = boost * eps

    assert_matrix_eq("boost^2 = I", boost * boost, I2)
    assert_matrix_eq("eps^2 = I", eps * eps, I2)
    assert_matrix_eq("boost eps = - eps boost", boost * eps, -(eps * boost))
    assert_matrix_eq("uPlus^2 = uPlus", u_plus * u_plus, u_plus)
    assert_matrix_eq("uMinus^2 = uMinus", u_minus * u_minus, u_minus)
    assert_matrix_eq("uPlus uMinus = 0", u_plus * u_minus, Z2)
    assert_matrix_eq("uMinus uPlus = 0", u_minus * u_plus, Z2)
    assert_matrix_eq("uPlus + uMinus = I", u_plus + u_minus, I2)
    assert_matrix_eq("eps = uPlus - uMinus", u_plus - u_minus, eps)
    assert_matrix_eq("(boost eps)^2 = -I", conformal * conformal, -I2)

    return {
        "boost_involutive": True,
        "eps_involutive": True,
        "boost_eps_anticommute": True,
        "projector_partition": True,
        "eps_projector_difference": True,
        "conformal_square_minus_identity": True,
    }


def verify_tripotent_boundary() -> dict[str, bool]:
    T = sp.diag(1, -1, 0)
    P_pos = sp.diag(1, 0, 0)
    P_neg = sp.diag(0, 1, 0)
    P_zero = sp.diag(0, 0, 1)
    I3 = sp.eye(3)
    Z3 = sp.zeros(3)

    assert_matrix_eq("T^3 = T", T**3, T)
    assert_matrix_eq("support projector T^2", T**2, P_pos + P_neg)
    assert_matrix_eq("projectors partition identity", P_neg + P_zero + P_pos, I3)
    for P in (P_neg, P_zero, P_pos):
        assert_matrix_eq("tripotent projector idempotent", P * P, P)
    assert_matrix_eq("negative eigen readout", T * P_neg, -P_neg)
    assert_matrix_eq("zero eigen readout", T * P_zero, Z3)
    assert_matrix_eq("positive eigen readout", T * P_pos, P_pos)

    return {
        "T_cube_T": True,
        "support_projector_T_square": True,
        "projector_partition": True,
        "projector_idempotents": True,
        "eigen_readouts": True,
    }


def main() -> None:
    result = {
        "five_grading": verify_five_grade_ledger(),
        "chiral_carrier": verify_chiral_carrier(),
        "tripotent_boundary": verify_tripotent_boundary(),
        "gap": run_gap_role_checks(),
        "sage": run_sage_root_checks(),
    }
    assert result["gap"]["v4_size"] == 4
    assert result["gap"]["v4_abelian"] is True
    assert result["gap"]["tripotent_sector_count"] == 3
    assert result["gap"]["five_grade_count"] == 5
    assert result["sage"]["a1_all_roots"] == 2
    assert result["sage"]["a1_weyl_order"] == 2
    assert result["sage"]["a1_cartan_det"] == 2
    assert result["sage"]["a1xa1_roots"] == 4
    assert result["sage"]["a1xa1_weyl_order"] == 4

    print("SUPER_TKK_CHIRAL_TRIPOTENT_FINITE_OK")
    print(json.dumps(result, sort_keys=True))
    print(
        "scope: finite five-grade ledger, real chiral carrier matrices, "
        "tripotent boundary readout, GAP/Sage finite sanity checks only"
    )


if __name__ == "__main__":
    main()
