#!/usr/bin/env python3
"""Symbolic PC flag filtration with the actual inverse peel factors.

All calculations are in GF(2)[e0,...,e5]/(ei^2-ei).  No Boolean values,
words, or carrier elements are enumerated.
"""
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

def inv_factor(k, parameter):
    return factor(inverses[k], parameter)

def zero(x):
    return red(x) == 0

p0 = M[2][7]
assert zero(p0 + e[0])
M1 = mm(inv_factor(0, p0), M)

p1 = M1[3][2]
assert zero(p1 + e[1])
M2 = mm(inv_factor(1, p1), M1)

p2 = M2[3][7]
assert zero(p2 + e[2])
M3 = mm(inv_factor(2, p2), M2)

p4 = M3[6][2]
assert zero(p4 + e[4])
p3 = red(M3[4][3] + p4)
assert zero(p3 + e[3])
M4 = mm(inv_factor(3, p3), M3)
M5 = mm(inv_factor(4, p4), M4)

p5 = red(M5[4][2])
assert zero(p5 + e[5])
M6 = mm(inv_factor(5, p5), M5)

residual = [(i, j, red(M6[i][j] + I[i][j]))
            for i in range(8) for j in range(8)
            if not zero(M6[i][j] + I[i][j])]
assert not residual, residual
print("FLAG_FILTRATION_INVERSE_SYMBOLIC=PASS")
print("FLAG_PIVOTS=e0:M[2,7];e1:M1[3,2];e2:M2[3,7];"
      "e4:M3[6,2];e3:M3[4,3]+e4;e5:M5[4,2]")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
