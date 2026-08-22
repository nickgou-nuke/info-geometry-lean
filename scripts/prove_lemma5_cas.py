#!/usr/bin/env python3
"""CAS proof of the final inverse-peeling pivot, without assignments."""
import re
import subprocess
import sympy as sp

raw = subprocess.run(["gap", "-q", "scripts/export_carrier_pc_rows.g"],
                     check=True, capture_output=True, text=True).stdout
rows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in part.split(",") if x]
            for part in m.group(2).split(";")]
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
C = [sp.Matrix([[int(j in rows[k][i]) for j in range(8)]
                 for i in range(8)]) for k in range(6)]
Inv = [a.inv_mod(2) for a in C]
def factor(a, q):
    return [[red(I[i][j] + q * (int(a[i, j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

M = I
for k in range(6):
    M = mm(M, factor(C[k], e[k]))
p0 = M[2][7]
M1 = mm(factor(Inv[0], p0), M)
p1 = M1[3][2]
M2 = mm(factor(Inv[1], p1), M1)
p2 = M2[3][7]
M3 = mm(factor(Inv[2], p2), M2)
p4 = M3[6][2]
p3 = red(M3[4][3] + p4)
M4 = mm(factor(C[3], p3), M3)
M5 = mm(factor(C[4], p4), M4)
assert red(M5[4][2] + e[5]) == 0
print("LEMMA_5_SYMBOLIC=PASS")
print("PIVOT=e5:M5[4,2]")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
