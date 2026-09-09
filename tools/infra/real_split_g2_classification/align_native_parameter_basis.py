"""Compute the rational change of basis for the Lean G2 root readout.

The script is only a witness producer.  Lean must replay its output before it
is used as a theorem.  Both inputs use the Zorn order
``(a, v0, v1, v2, b, w0, w1, w2)``; the circular readout is conjugated back to
that standard order with the rational frame matrix.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean/InfoGeometry/Lie/CanonicalZornG2NativeMatrixExport.lean"
CAS = Path(__file__).resolve().parent / "artifacts/real_split_g2_exact_ca_certificate.json"
OUT = ROOT / "artifacts/real_split_g2_native_basis_alignment.json"


def q(text: str) -> sp.Rational:
    text = re.sub(r"\s*:\s*ℚ", "", text)
    text = text.strip().replace("(", "").replace(")", "").replace(" ", "")
    if text == "0":
        return sp.Rational(0)
    if "/" in text:
        a, b = text.split("/", 1)
        return sp.Rational(int(a), int(b))
    return sp.Rational(int(text))


def matrix_literal(block: str) -> sp.Matrix:
    rows = []
    for row in block.split(";"):
        row = row.replace("!![", "").replace("]", "")
        rows.append([q(x) for x in row.split(",") if x.strip()])
    if len(rows) != 8 or any(len(row) != 8 for row in rows):
        raise ValueError(f"expected 8x8 literal, got {list(map(len, rows))}")
    return sp.Matrix(rows)


def read_lean_tables() -> tuple[sp.Matrix, list[sp.Matrix]]:
    source = LEAN.read_text()
    frame_text = re.search(
        r"def rationalCircularFrameMatrix.*?explicitInverseMatrix :=\n\s*!!\[(.*?)\]\n\n",
        source,
        re.S,
    )
    # The frame itself is the first 8x8 literal in the inverse proof.
    frame_text = re.search(
        r"have hframe :.*?!!\[(.*?)\] := by", source, re.S
    )
    if not frame_text:
        raise ValueError("rational frame literal not found")
    frame = matrix_literal(frame_text.group(1))
    table_text = re.search(
        r"def rootDerivationRationalTable.*?^  \]\n\nset_option",
        source,
        re.S | re.M,
    )
    if not table_text:
        raise ValueError("root table not found")
    blocks = re.findall(r"\(!!\[(.*?)\]\)", table_text.group(0), re.S)
    if len(blocks) != 14:
        raise ValueError(f"expected 14 root matrices, got {len(blocks)}")
    return frame, [matrix_literal(block) for block in blocks]


def main() -> None:
    frame, circular = read_lean_tables()
    if frame.det() == 0:
        raise ValueError("Lean rational frame is singular")
    cas = json.loads(CAS.read_text())
    cas_basis = [sp.Matrix(item) for item in cas["basis_matrices"]]
    # CAS order is (a,b,v0,v1,v2,w0,w1,w2), while Lean is
    # (a,v0,v1,v2,b,w0,w1,w2).  Conjugate operators into Lean order.
    lean_from_cas = [0, 2, 3, 4, 1, 5, 6, 7]
    cas_basis = [
        matrix.extract(lean_from_cas, lean_from_cas) for matrix in cas_basis
    ]
    cas_matrix = sp.Matrix.hstack(
        *[sp.Matrix(m).reshape(64, 1) for m in cas_basis]
    )
    candidates = {}
    for transpose_cas in (False, True):
        cas_for_compare = [matrix.T if transpose_cas else matrix for matrix in cas_basis]
        cas_matrix = sp.Matrix.hstack(
            *[sp.Matrix(m).reshape(64, 1) for m in cas_for_compare]
        )
        for transpose_native in (False, True):
            for orientation, build in (
                ("frame_operator_frame_inv", lambda matrix: frame * matrix * frame.inv()),
                ("frame_inv_operator_frame", lambda matrix: frame.inv() * matrix * frame),
            ):
                name = f"casT={transpose_cas},nativeT={transpose_native},{orientation}"
                candidates[name] = [
                    build(matrix).T if transpose_native else build(matrix)
                    for matrix in circular
                ]
    solved = []
    for name, standard in candidates.items():
        native = sp.Matrix.hstack(*[sp.Matrix(m).reshape(64, 1) for m in standard])
        print(f"{name}: native_rank={native.rank()} combined_rank={native.row_join(cas_matrix).rank()}")
        if native.rank() == 14 and native.row_join(cas_matrix).rank() == 14:
            solved.append((name, native))
    preferred = "casT=False,nativeT=False,frame_operator_frame_inv"
    if preferred not in candidates:
        raise AssertionError("preferred Lean column-action convention missing")
    name = preferred
    native = sp.Matrix.hstack(*[
        sp.Matrix(m).reshape(64, 1)
        for m in candidates[name]
    ])
    cas_matrix = sp.Matrix.hstack(
        *[sp.Matrix(m).reshape(64, 1) for m in cas_basis]
    )
    if native.row_join(cas_matrix).rank() != 14:
        raise ValueError("Lean column-action convention does not align CAS basis")
    # P has native-root columns: CAS basis = native basis * P.
    p = native.gauss_jordan_solve(cas_matrix)[0]
    if native * p != cas_matrix:
        raise AssertionError("basis alignment equation failed")
    if p.det() == 0:
        raise AssertionError("alignment matrix is singular")
    OUT.write_text(json.dumps({
        "coordinate_order": ["a", "v0", "v1", "v2", "b", "w0", "w1", "w2"],
        "orientation": name,
        "equation": "B_CAS = B_native * P",
        "determinant": str(p.det()),
        "matrix": [[str(p[i, j]) for j in range(14)] for i in range(14)],
    }, indent=2) + "\n")
    print(f"ALIGNMENT_OK det={p.det()} output={OUT}")


if __name__ == "__main__":
    main()
