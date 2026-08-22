#!/usr/bin/env python3
"""CAS proof of the second inverse-peeling pivot, without assignments."""
import re
import subprocess
import sympy as sp

raw = subprocess.run(
    ["gap", "-q", "scripts/export_carrier_pc_rows.g"],
    check=True, capture_output=True, text=True,
).stdout
rows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in part.split(",") if x]
            for part in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")

def red(x):
    p = sp.Poly(sp.expand(x), *e, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(e, mon):
                if power:
                    term *= v
            out += term
    return sp.Poly(out, *e, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
constants = [sp.Matrix([[int(j in rows[k][i]) for j in range(8)]
                         for i in range(8)]) for k in range(6)]
inverses = [a.inv_mod(2) for a in constants]

def factor(a, parameter):
    return [[red(I[i][j] + parameter * (int(a[i, j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

M = I
for k in range(6):
    M = mm(M, factor(constants[k], e[k]))

p0 = M[2][7]
assert red(p0 + e[0]) == 0
M1 = mm(factor(inverses[0], p0), M)

p1 = M1[3][2]
assert red(p1 + e[1]) == 0
print("LEMMA_1_SYMBOLIC=PASS")
print("PIVOT=e1:M1[3,2]")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
