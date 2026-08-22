#!/usr/bin/env python3
"""Symbolic fixed-basis CAS certificate for the next complement generator."""

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
    matrix_word = (identity + a[index] * (generators[index] - identity)) * matrix_word

target = swap * generators[2] * swap
equations = [matrix_word[i, j] - target[i, j]
             for i in range(8) for j in range(8)]
groebner = sp.groebner(
    equations + [bit * bit + bit for bit in a], *a, order="lex", modulus=2
)
expected = [1, 0, 0, 0, 1, 1]
assert [str(poly.as_expr()) for poly in groebner.polys] == [
    "a0 + 1", "a1", "a2", "a3", "a4 + 1", "a5 + 1"
]
assert all(
    sp.Poly(matrix_word[i, j].subs(dict(zip(a, expected))) - target[i, j],
            *a, modulus=2).as_expr() == 0
    for i in range(8) for j in range(8)
)

print("BN2_SECOND_CONJUGATION_FIXED_BASIS=PASS")
print("s * p2 * s = pcWord [1,0,0,0,1,1]")
print("GROEBNER_NO_ASSIGNMENT_ENUMERATION=PASS")
