#!/usr/bin/env python3
"""Finite verifier for the sedenion spinor / Cuntz / Drazin bridge.

Source digest: `preprints202605.0168.v1` uses steering spinors `S` in five
triplet sectors Γ, Θ, U, V, W inside a 16-dimensional sedenion carrier.  The
paper's analytic gravity/cosmology claims are intentionally not asserted here.

Checked finite corridor:
  * `1 + 5*3 = 16` steering-sector bookkeeping;
  * Cayley-Dickson sedenion basis atoms `e_i^2 = -1` and one nonzero
    associator witness;
  * bilinear symmetric/skew decomposition;
  * finite matrix-unit Cuntz projection shadows for O5 and O16;
  * tripotent/Drazin support/null readout;
  * GAP/Sage/clifford/galgebra sanity lanes.
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

Vec = tuple[int, ...]


def add(x: Vec, y: Vec) -> Vec:
    return tuple(a + b for a, b in zip(x, y, strict=True))


def sub(x: Vec, y: Vec) -> Vec:
    return tuple(a - b for a, b in zip(x, y, strict=True))


def neg(x: Vec) -> Vec:
    return tuple(-a for a in x)


def conj(x: Vec) -> Vec:
    if len(x) == 1:
        return x
    h = len(x) // 2
    return conj(x[:h]) + neg(x[h:])


def cd_mul(x: Vec, y: Vec) -> Vec:
    """Cayley-Dickson multiplication, doubled to dimension 16."""
    if len(x) == 1:
        return (x[0] * y[0],)
    h = len(x) // 2
    a, b = x[:h], x[h:]
    c, d = y[:h], y[h:]
    left = sub(cd_mul(a, c), cd_mul(conj(d), b))
    right = add(cd_mul(d, a), cd_mul(b, conj(c)))
    return left + right


def basis(n: int, i: int) -> Vec:
    return tuple(1 if k == i else 0 for k in range(n))


def assert_vec(label: str, actual: Vec, expected: Vec) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: actual={actual}, expected={expected}")


def matrix_unit(n: int, i: int, j: int) -> sp.Matrix:
    m = sp.zeros(n)
    m[i, j] = 1
    return m


def run_gap_checks() -> dict[str, int | bool]:
    script = r'''
Sectors := SymmetricGroup(5);;
Triplet := SymmetricGroup(3);;
result := Concatenation(
  "{\"sector_count\":", String(5),
  ",\"triplet_count\":", String(3),
  ",\"basis_count\":", String(1 + 5 * 3),
  ",\"sector_perm_order\":", String(Size(Sectors)),
  ",\"triplet_perm_order\":", String(Size(Triplet)),
  ",\"sector_triplet_perm_order\":", String(Size(Sectors) * Size(Triplet)),
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


def run_sage_checks() -> dict[str, int]:
    sage_file = ROOT / ".tmp_sedenion_spinor_cuntz_drazin.sage"
    sage_file.write_text(
        r'''
import json
from builtins import int as py_int
V = VectorSpace(QQ, 16)
A1 = RootSystem(['A', 1])
W1 = WeylGroup(['A', 1])
result = {
  "vector_space_dim": py_int(V.dimension()),
  "sector_count": py_int(5),
  "triplet_count": py_int(3),
  "basis_count": py_int(1 + 5 * 3),
  "a1_roots": py_int(2 * len(list(A1.root_poset()))),
  "a1_weyl_order": py_int(W1.order()),
}
print(json.dumps(result, sort_keys=True))
'''
    )
    try:
        out = subprocess.check_output([str(SAGE), str(sage_file)], text=True)
    finally:
        sage_file.unlink(missing_ok=True)
    return json.loads(out.strip().splitlines()[-1])


def verify_sedenion_atoms() -> dict[str, object]:
    one = basis(16, 0)
    minus_one = (-1,) + (0,) * 15

    for i in range(1, 16):
        assert_vec(f"e{i}^2 = -1", cd_mul(basis(16, i), basis(16, i)), minus_one)

    witness = None
    for i in range(1, 16):
        for j in range(1, 16):
            for k in range(1, 16):
                left = cd_mul(cd_mul(basis(16, i), basis(16, j)), basis(16, k))
                right = cd_mul(basis(16, i), cd_mul(basis(16, j), basis(16, k)))
                assoc = sub(left, right)
                if assoc != (0,) * 16:
                    witness = {"i": i, "j": j, "k": k, "associator": assoc}
                    break
            if witness:
                break
        if witness:
            break
    if witness is None:
        raise AssertionError("expected a nonzero sedenion associator witness")

    # Zero-divisor sanity: (e3 + e10)(e6 - e15) is a known sedenion-style pattern
    # under many conventions, but conventions vary; keep only the proven
    # non-associator as the mandatory CD check.
    assert_vec("e0 is left unit", cd_mul(one, basis(16, 7)), basis(16, 7))
    assert_vec("e0 is right unit", cd_mul(basis(16, 7), one), basis(16, 7))

    return {
        "basis_dim": 16,
        "imaginary_squares_minus_one": True,
        "nonzero_associator_witness": witness,
    }


def verify_sector_and_bilinear() -> dict[str, bool]:
    sectors = ["Gamma", "Theta", "U", "V", "W"]
    assert 1 + len(sectors) * 3 == 16

    B = sp.Matrix(
        [
            [1, 2, 3, 4, 5],
            [7, 11, 13, 17, 19],
            [23, 29, 31, 37, 41],
            [43, 47, 53, 59, 61],
            [67, 71, 73, 79, 83],
        ]
    )
    sym = B + B.T
    skew = B - B.T
    assert_matrix_eq("symmetric readout", sym.T, sym)
    assert_matrix_eq("skew readout", skew.T, -skew)
    assert_matrix_eq("bilinear reconstruction", (sym + skew) / 2, B)

    return {
        "one_plus_five_triplets_is_sixteen": True,
        "symmetric_readout": True,
        "skew_readout": True,
        "bilinear_reconstruction": True,
    }


def verify_cuntz_shadow(n: int) -> dict[str, bool]:
    V = [matrix_unit(n, i, 0) for i in range(n)]
    P0 = matrix_unit(n, 0, 0)
    I = sp.eye(n)
    Z = sp.zeros(n)
    for i in range(n):
        for j in range(n):
            assert_matrix_eq(
                f"O{n} source overlap {i},{j}",
                V[i].T * V[j],
                P0 if i == j else Z,
            )
    projections = [v * v.T for v in V]
    assert_matrix_eq(f"O{n} range projections sum one", sum(projections, Z), I)
    for i, p in enumerate(projections):
        assert_matrix_eq(f"O{n} range projection {i} idempotent", p * p, p)
    for i in range(n):
        for j in range(n):
            if i != j:
                assert_matrix_eq(f"O{n} orthogonal range {i},{j}", projections[i] * projections[j], Z)
    return {
        "matrix_unit_partial_isometry_shadow": True,
        "range_projection_partition": True,
        "range_projection_orthogonal": True,
    }


def verify_drazin_tripotent() -> dict[str, bool]:
    T = sp.diag(1, -1, 0)
    D = T
    P_d = T * D
    P_null = sp.eye(3) - P_d
    assert_matrix_eq("T^3 = T", T**3, T)
    assert_matrix_eq("Drazin DAD = D", D * T * D, D)
    assert_matrix_eq("Drazin commutes", T * D, D * T)
    assert_matrix_eq("Drazin index-1 law", T**2 * D, T)
    assert_matrix_eq("Drazin support T^2", P_d, T**2)
    assert_matrix_eq("support idempotent", P_d * P_d, P_d)
    assert_matrix_eq("tripotent annihilates null", T * P_null, sp.zeros(3))
    return {
        "tripotent": True,
        "own_drazin_inverse_index_one": True,
        "support_projector": True,
        "null_projector_annihilated": True,
    }


def verify_clifford_dimension_lane() -> dict[str, int | bool]:
    import clifford  # type: ignore

    layout, blades = clifford.Cl(0, 4)
    e1 = blades["e1"]
    return {
        "cl04_dim": len(layout.blades),
        "e1_square_minus_one": int((e1 * e1)(0)) == -1,
    }


def verify_galgebra_dimension_lane() -> dict[str, bool | int]:
    from galgebra.ga import Ga  # type: ignore

    g = Ga("e1 e2 e3 e4", g=[-1, -1, -1, -1])
    e = list(g.mv_basis)
    return {
        "basis_vector_count": len(e),
        "e1_square_minus_one": str(e[0] * e[0]) == "-1",
    }


def main() -> None:
    result = {
        "pdf_digest": {
            "title": "Emergent Quantum Gravity from Sedenion Spinor Geometry",
            "closed_formal_lane": "finite steering-sector/Cuntz/Drazin/operator-shadow algebra only",
            "open_debt": [
                "full sedenion formalization in Lean",
                "spinor bundle/tetrad/connection construction",
                "Einstein equations and Yukawa potential",
                "cosmology/dark matter/dark energy claims",
                "faithful infinite-dimensional Cuntz representation",
            ],
        },
        "sector_bilinear": verify_sector_and_bilinear(),
        "sedenion": verify_sedenion_atoms(),
        "cuntz_O5_shadow": verify_cuntz_shadow(5),
        "cuntz_O16_shadow": verify_cuntz_shadow(16),
        "drazin_tripotent": verify_drazin_tripotent(),
        "gap": run_gap_checks(),
        "sage": run_sage_checks(),
        "clifford": verify_clifford_dimension_lane(),
        "galgebra": verify_galgebra_dimension_lane(),
    }
    assert result["gap"]["basis_count"] == 16
    assert result["gap"]["sector_perm_order"] == 120
    assert result["sage"]["vector_space_dim"] == 16
    assert result["clifford"]["cl04_dim"] == 16
    print("SEDENION_SPINOR_CUNTZ_DRAZIN_FINITE_OK")
    print(json.dumps(result, sort_keys=True, default=str))
    print(
        "scope: finite sector bookkeeping, Cayley-Dickson associator witness, "
        "Cuntz matrix-unit projection shadows, Drazin tripotent support, "
        "and Sage/GAP/clifford/galgebra sanity checks only"
    )


if __name__ == "__main__":
    main()
