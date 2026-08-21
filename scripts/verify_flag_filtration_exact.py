#!/usr/bin/env python3
"""Symbolic PC flag-filtration certificate for the six GAP generators.

The certificate uses the actual GAP carrier rows and Boolean polynomial
reduction.  It performs no assignment or word enumeration.  Matrix
multiplication follows the Lean owner convention
`autMatrix (f * g) = autMatrix g * autMatrix f`.
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
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")

def rb(expr):
    poly = sp.Poly(sp.expand(expr), *e, modulus=2)
    out = 0
    for mon, coeff in poly.terms():
        if int(coeff) & 1:
            term = 1
            for var, power in zip(e, mon):
                if power:
                    term *= var
            out += term
    return sp.Poly(out, *e, modulus=2).as_expr()

def mm(left, right):
    return [[rb(sum(left[i][k] * right[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]

def generator_matrix(k, parameter):
    support = rows[k]
    return [[rb(I[i][j] + parameter *
                (int(j in support[i]) + I[i][j]))
             for j in range(8)] for i in range(8)]

def check_zero(M):
    return all(rb(x) == 0 for row in M for x in row)

# M is the matrix of p0^e0 * ... * p5^e5 in the Lean orientation.
M = I
for k in range(6):
    M = mm(generator_matrix(k, e[k]), M)

def bit(name):
    return e[name]

# Each pivot is read from the current quotient and then peeled on the right.
p0 = M[2][7]
assert rb(p0 + bit(0)) == 0
M1 = mm(M, generator_matrix(0, p0))

p1 = M1[3][2]
assert rb(p1 + bit(1)) == 0
M2 = mm(M1, generator_matrix(1, p1))

p2 = M2[0][2]
assert rb(p2 + bit(2)) == 0
M3 = mm(M2, generator_matrix(2, p2))

p4 = M3[0][7]
assert rb(p4 + bit(4)) == 0
p3 = rb(M3[4][3] + p4)
assert rb(p3 + bit(3)) == 0
M4 = mm(M3, generator_matrix(3, p3))
M5 = mm(M4, generator_matrix(4, p4))

p5 = M5[4][2]
p5 = rb(p5 + bit(1) + bit(2))
assert rb(p5 + bit(5)) == 0
M6 = mm(M5, generator_matrix(5, p5))
print("DEBUG_M6_RESIDUAL=", [(i, j, rb(M6[i][j] + I[i][j]))
                             for i in range(8) for j in range(8)
                             if rb(M6[i][j] + I[i][j]) != 0])
assert check_zero([[M6[i][j] + I[i][j] for j in range(8)]
                   for i in range(8)])

print("FLAG_FILTRATION_GAP_ROWS=PASS")
print("FLAG_PIVOTS=e0:m[2,7];e1:m1[3,2];e2:m2[0,2];"
      "e4:m3[0,7];e3:m3[4,3]+e4;e5:m5[4,2]+e1+e2")
print("FLAG_FILTRATION_SYMBOLIC=PASS")
print("FLAG_FILTRATION_NO_ASSIGNMENT_ENUMERATION=PASS")
