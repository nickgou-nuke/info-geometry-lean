#!/usr/bin/env python3
"""Gröbner certificates for all complement conjugations by ``swap01Aut``.

The fixed Lean carrier matrices are imported from GAP only as exact matrix
rows.  Each six-coordinate word is solved symbolically modulo the Boolean
ideal; no carrier elements or assignments are enumerated.
"""

from pathlib import Path
import re
import subprocess
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
raw = subprocess.run(
    ["gap", "-q", str(ROOT / "scripts/export_carrier_pc_rows.g")],
    cwd=ROOT, check=True, capture_output=True, text=True,
).stdout
rows = {}
for line in raw.splitlines():
    match = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if match:
        rows[int(match.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in match.group(2).split(";")
        ]
assert set(rows) == set(range(6))

a = sp.symbols("a0:6")
identity = sp.eye(8)
generators = [sp.Matrix([
    [int(j in rows[k][i]) for j in range(8)] for i in range(8)
]) for k in range(6)]
swap = identity.copy()
for left, right in ((2, 3), (5, 6)):
    swap[left, left] = swap[right, right] = 0
    swap[left, right] = swap[right, left] = 1

matrix_word = identity
for index in range(6):
    matrix_word = (identity + a[index] *
                   (generators[index] - identity)) * matrix_word

expected = {
    0: [0, 0, 1, 0, 1, 1],
    2: [1, 0, 0, 0, 1, 1],
    3: [0, 0, 0, 0, 0, 1],
    4: [0, 0, 0, 1, 1, 1],
    5: [0, 0, 0, 1, 0, 0],
}
for index, vector in expected.items():
    target = swap * generators[index] * swap
    equations = [matrix_word[i, j] - target[i, j]
                 for i in range(8) for j in range(8)]
    basis = sp.groebner(
        equations + [bit * bit + bit for bit in a],
        *a, order="lex", modulus=2,
    )
    assert all(
        sp.Poly(matrix_word[i, j].subs(dict(zip(a, vector))) - target[i, j],
                *a, modulus=2).as_expr() == 0
        for i in range(8) for j in range(8)
    )
    assert len(basis.polys) == 6
    print(f"S_COMPLEMENT_CONJUGATION_P{index}=PASS")
    print(f"s * p{index} * s = pcWord {vector}")

print("S_COMPLEMENT_GROEBNER_PACKET=PASS")
print("GROEBNER_NO_ASSIGNMENT_ENUMERATION=PASS")
