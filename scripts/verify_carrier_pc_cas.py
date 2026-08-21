#!/usr/bin/env python3
"""CAS-to-CAS validation of the carrier PC normal form.

GAP derives the PC generators from the actual carrier Sylow subgroup.  This
script consumes GAP's machine-readable row export and symbolically proves the
resulting matrices preserve the GF(2) split-Zorn product and satisfy the PC
power relations.  It is a CAS gate; it is deliberately not imported by Lean.
"""

from pathlib import Path
import subprocess
import re

import numpy as np
from sympy import Poly, symbols

ROOT = Path(__file__).resolve().parents[1]
gap_script = ROOT / "scripts" / "derive_carrier_b_pc_normal_form.g"
run = subprocess.run(
    ["gap", "-q", str(gap_script)],
    cwd=ROOT,
    check=True,
    capture_output=True,
    text=True,
)
if run.stderr:
    raise AssertionError(f"GAP emitted diagnostics: {run.stderr}")

rows_by_name = {}
power_relations = {}
conjugation_relations = {}
for line in run.stdout.splitlines():
    match = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if match:
        rows = []
        for block in match.group(2).split(";"):
            rows.append(tuple(int(x) - 1 for x in block.split(",") if x))
        if len(rows) != 8:
            raise AssertionError(f"bad PCROW: {line}")
        rows_by_name[f"p{match.group(1)}"] = tuple(rows)
        continue
    match = re.fullmatch(r"PCPOWER ([1-6]) ([0-9]+) ([0-9,]*)", line.strip())
    if match:
        power_relations[int(match.group(1)) - 1] = tuple(
            int(x) for x in match.group(3).split(",") if x
        )
        continue
    match = re.fullmatch(r"PCCONJ ([1-6]) ([1-6]) ([0-9,]*)", line.strip())
    if match:
        conjugation_relations[(int(match.group(1)) - 1,
                               int(match.group(2)) - 1)] = tuple(
            int(x) for x in match.group(3).split(",") if x
        )

if set(rows_by_name) != {f"p{i}" for i in range(1, 7)}:
    raise AssertionError(f"missing GAP PC rows: {sorted(rows_by_name)}")

def xor(*terms):
    return sum(terms)

def zorn_mul(left, right):
    a, b, x0, x1, x2, y0, y1, y2 = left
    A, B, X0, X1, X2, Y0, Y1, Y2 = right
    return (
        xor(a * A, x0 * Y0, x1 * Y1, x2 * Y2),
        xor(b * B, y0 * X0, y1 * X1, y2 * X2),
        xor(a * X0, B * x0, y1 * Y2, y2 * Y1),
        xor(a * X1, B * x1, y2 * Y0, y0 * Y2),
        xor(a * X2, B * x2, y0 * Y1, y1 * Y0),
        xor(A * y0, b * Y0, x1 * X2, x2 * X1),
        xor(A * y1, b * Y1, x2 * X0, x0 * X2),
        xor(A * y2, b * Y2, x0 * X1, x1 * X0),
    )

z = symbols("a x0 x1 x2 y0 y1 y2 b")
z2 = symbols("A X0 X1 X2 Y0 Y1 Y2 B")

def apply(matrix, vector):
    return tuple(
        xor(*(int(matrix[i, j]) * vector[j] for j in range(8)))
        for i in range(8)
    )

def matrix_of_rows(rows):
    matrix = np.zeros((8, 8), dtype=int)
    for i, columns in enumerate(rows):
        for j in columns:
            matrix[i, j] ^= 1
    return matrix

def symbolic_automorphism(matrix):
    mapped_product = apply(matrix, zorn_mul(z, z2))
    product_of_mapped = zorn_mul(apply(matrix, z), apply(matrix, z2))
    return all(
        Poly(lhs - rhs, *z, *z2, modulus=2).is_zero
        for lhs, rhs in zip(mapped_product, product_of_mapped)
    )

pc = [matrix_of_rows(rows_by_name[f"p{i}"]) for i in range(1, 7)]
assert all(symbolic_automorphism(matrix) for matrix in pc)
identity = np.eye(8, dtype=int)

def pc_word(exponents):
    result = identity.copy()
    for matrix, exponent in zip(pc, exponents):
        for _ in range(exponent):
            result = (result @ matrix) % 2
    return result

def matrix_inverse_from_order(matrix):
    current = identity.copy()
    for _ in range(1, 9):
        current = (current @ matrix) % 2
        if np.array_equal(current, identity):
            return np.linalg.matrix_power(matrix, _ - 1) % 2
    raise AssertionError("PC generator inverse was not found")

# GAP's PC presentation has p2^2 = p6 and p3^2 = p6; the others square to 1.
assert np.array_equal((pc[0] @ pc[0]) % 2, identity)
assert np.array_equal((pc[1] @ pc[1]) % 2, pc[5])
assert np.array_equal((pc[2] @ pc[2]) % 2, pc[5])
for i in (3, 4, 5):
    assert np.array_equal((pc[i] @ pc[i]) % 2, identity)
assert len(power_relations) == 6
for i, exponents in power_relations.items():
    assert np.array_equal(np.linalg.matrix_power(pc[i], 2) % 2,
                          pc_word(exponents))
assert len(conjugation_relations) == 15
for (i, j), exponents in conjugation_relations.items():
    lhs = (matrix_inverse_from_order(pc[i]) @ pc[j] @ pc[i]) % 2
    assert np.array_equal(lhs, pc_word(exponents))

print("GAP -> symbolic PC row transport: PASS")
print("All six GAP-derived PC matrices preserve split-Zorn multiplication")
print("GAP PC power relations: PASS")
print("GAP PC conjugation relations (15): PASS")
