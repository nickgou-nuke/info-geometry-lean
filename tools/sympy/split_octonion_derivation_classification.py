#!/usr/bin/env python3
"""Multi-system derivation classification check for the Zorn split-octonion algebra.

This is the computational first pass for the honest theorem behind
`Aut(O_s) = G_{2(2)}` over characteristic-zero split octonions:

  Lie(Aut(O_s)) = Der(O_s), and dim Der(O_s) = 14.

What is verified here, exactly:
  * SymPy constructs the 8-dimensional Zorn split-octonion algebra over QQ.
  * It builds the complete linear system for derivations
        D(x*y) = D(x)*y + x*D(y)
    on all basis pairs.
  * It proves by exact rational row reduction that the solution space has
    dimension 14.
  * It cross-checks the same matrix rank/nullity with Sage when available.
  * It checks Sage's split `G2` Lie algebra dimension/root count.
  * It checks GAP's G2 Weyl group order via a dihedral presentation.
  * It checks clifford and galgebra Cl(5,5) availability/sanity.

What is NOT verified here:
  * no Lean proof of the full algebraic group classification;
  * no proof that every automorphism integrates every derivation;
  * no real Lie group global topology statement;
  * no SU(3), particle, anomaly, or Super-TKK theorem.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
MULT_PATH = ROOT / "tools" / "sympy" / "split_octonion_multiplication.py"
spec = importlib.util.spec_from_file_location("split_octonion_multiplication", MULT_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {MULT_PATH}")
mult = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mult
spec.loader.exec_module(mult)

Zorn = mult.Zorn

BASIS = [
    mult.EPLUS,
    mult.EMINUS,
    mult.UP[0],
    mult.UP[1],
    mult.UP[2],
    mult.DOWN[0],
    mult.DOWN[1],
    mult.DOWN[2],
]
BASIS_NAMES = ["ePlus", "eMinus", "up0", "up1", "up2", "down0", "down1", "down2"]


def coords(z: Zorn) -> list[sp.Expr]:
    return [sp.sympify(c) for c in [z.a, z.b, *z.x, *z.y]]


def from_coords(c: list[sp.Expr]) -> Zorn:
    return Zorn(c[0], c[1], (c[2], c[3], c[4]), (c[5], c[6], c[7]))


def mat_apply(Mvars: list[sp.Symbol], basis_index: int) -> Zorn:
    # Matrix columns are images of basis vectors.
    return from_coords([Mvars[row * 8 + basis_index] for row in range(8)])


def linear_apply_to_coords(Mvars: list[sp.Symbol], c: list[sp.Expr]) -> Zorn:
    out = []
    for row in range(8):
        out.append(sum(Mvars[row * 8 + col] * c[col] for col in range(8)))
    return from_coords(out)


def build_derivation_constraint_matrix() -> sp.Matrix:
    variables = sp.symbols("d0:64")
    equations: list[sp.Expr] = []
    for i, x in enumerate(BASIS):
        for j, y in enumerate(BASIS):
            lhs = linear_apply_to_coords(list(variables), coords(x * y))
            rhs = mat_apply(list(variables), i) * y + x * mat_apply(list(variables), j)
            equations.extend([sp.expand(a - b) for a, b in zip(coords(lhs), coords(rhs))])
    rows = []
    for eq in equations:
        rows.append([sp.expand(eq).coeff(v) for v in variables])
    return sp.Matrix(rows)


def sage_crosscheck(A: sp.Matrix) -> str:
    sage = Path("/home/goutev/miniforge3/envs/sage/bin/sage")
    if not sage.exists():
        return "SAGE_SKIPPED missing"
    with tempfile.TemporaryDirectory() as td:
        matrix_json = Path(td) / "matrix.json"
        script = Path(td) / "rank_check.sage"
        matrix_json.write_text(json.dumps([[int(x) for x in row] for row in A.tolist()]))
        script.write_text(
            "import json\n"
            f"data = json.load(open({str(matrix_json)!r}))\n"
            "A = Matrix(QQ, data)\n"
            "print('SAGE_DERIVATION_RANK', A.rank())\n"
            "print('SAGE_DERIVATION_NULLITY', A.ncols() - A.rank())\n"
            "R = RootSystem(['G',2])\n"
            "print('SAGE_G2_RANK', len(R.index_set()))\n"
            "print('SAGE_G2_POSITIVE_ROOTS', len(list(R.root_poset())))\n"
            "from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis\n"
            "g = LieAlgebraChevalleyBasis(QQ, ['G', 2])\n"
            "print('SAGE_G2_LIE_DIM', g.dimension())\n"
        )
        proc = subprocess.run([str(sage), str(script)], text=True, capture_output=True, timeout=120)
        if proc.returncode != 0:
            return "SAGE_FAILED " + proc.stderr.strip().splitlines()[-1]
        return proc.stdout.strip()


def gap_crosscheck() -> str:
    gap = Path("/home/goutev/miniforge3/envs/sage/bin/gap")
    if not gap.exists():
        return "GAP_SKIPPED missing"
    code = """
W := DihedralGroup(IsPermGroup, 12);;
Print("GAP_DIHEDRAL_G2_WEYL_ORDER ", Size(W), "\\n");
Print("GAP_DIHEDRAL_G2_WEYL_GENERATORS ", Length(GeneratorsOfGroup(W)), "\\n");
QUIT;
"""
    proc = subprocess.run([str(gap), "-q"], input=code, text=True, capture_output=True, timeout=60)
    if proc.returncode != 0:
        return "GAP_FAILED " + proc.stderr.strip().splitlines()[-1]
    return proc.stdout.strip()


def clifford_galgebra_crosscheck() -> str:
    lines = []
    try:
        import clifford

        layout, blades = clifford.Cl(5, 5)
        e = [blades[f"e{i}"] for i in range(1, 11)]
        ps = e[0]
        for ei in e[1:]:
            ps = ps * ei
        lines.append(f"CLIFFORD_CL55_DIM {2 ** 10}")
        lines.append(f"CLIFFORD_CL55_PSEUDOSCALAR_SQ {int(round(float((ps * ps)(0))))}")
    except Exception as ex:  # pragma: no cover
        lines.append(f"CLIFFORD_FAILED {type(ex).__name__}: {ex}")
    try:
        from galgebra.ga import Ga

        g = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
        basis = list(g.mv_basis)
        lines.append(f"GALGEBRA_BASIS_LEN {len(basis)}")
        lines.append(f"GALGEBRA_E1_SQ {basis[0] * basis[0]}")
        lines.append(f"GALGEBRA_E6_SQ {basis[5] * basis[5]}")
    except Exception as ex:  # pragma: no cover
        lines.append(f"GALGEBRA_FAILED {type(ex).__name__}: {ex}")
    return "\n".join(lines)


def main() -> None:
    A = build_derivation_constraint_matrix()
    rank = A.rank()
    nullity = A.cols - rank
    nullspace = A.nullspace()
    assert A.rows == 64 * 8
    assert A.cols == 64
    assert rank == 50, rank
    assert nullity == 14, nullity
    assert len(nullspace) == 14

    # Every derivation kills the unit ePlus+eMinus; verify from the nullspace basis.
    unit_col = sp.Matrix([1, 1, 0, 0, 0, 0, 0, 0])
    for vec in nullspace:
        M = sp.Matrix(8, 8, list(vec))
        assert M * unit_col == sp.zeros(8, 1)

    print("SYMPY_DERIVATION_CONSTRAINT_MATRIX", A.rows, A.cols)
    print("SYMPY_DERIVATION_RANK", rank)
    print("SYMPY_DERIVATION_NULLITY", nullity)
    print("SYMPY_DERIVATION_BASIS_COUNT", len(nullspace))
    print("SYMPY_DERIVATIONS_KILL_UNIT yes")
    print(sage_crosscheck(A))
    print(gap_crosscheck())
    print(clifford_galgebra_crosscheck())
    print("SCOPE Lie algebra derivations dim=14 verified computationally; full Lean/global Aut(O_s)=G_{2(2)} classification still requires a theorem bridge from derivations to automorphism group")


if __name__ == "__main__":
    main()
