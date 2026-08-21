#!/usr/bin/env python3
"""Derive triangular PC-word coordinate separators symbolically.

The matrices are imported from GAP.  Matrix entries are reduced in the
Boolean polynomial ring; no values of the six Boolean parameters are tested.
"""

from pathlib import Path
import re
import subprocess
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
out = subprocess.run(
    ["gap", "-q", str(ROOT / "scripts/export_carrier_pc_rows.g")],
    cwd=ROOT, check=True, capture_output=True, text=True,
)
rows = {}
for line in out.stdout.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")

def rb(expr):
    p = sp.Poly(sp.expand(expr), *e, modulus=2)
    result = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for var, exponent in zip(e, mon):
                if exponent:
                    term *= var
            result += term
    return sp.Poly(result, *e, modulus=2).as_expr()

def matrix(i):
    return [[int(j in rows[i][r]) for j in range(8)] for r in range(8)]

def mm(a, b):
    return [[rb(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
def factor(i):
    p = matrix(i)
    return [[rb(I[r][c] + e[i] * (p[r][c] + I[r][c]))
             for c in range(8)] for r in range(8)]

M = I
for i in range(6):
    M = mm(M, factor(i))

for k in range(6):
    found = []
    for i in range(8):
        for j in range(8):
            q = rb(M[i][j].subs(e[k], 0))
            delta = rb(M[i][j].subs(e[k], 1) + q)
            if delta == 1 and all(
                not mon[k2] for mon in sp.Poly(q, *e, modulus=2).monoms()
                for k2 in [k]
            ) and all(
                all(mon[l] == 0 for l in range(k + 1, 6))
                for mon in sp.Poly(q, *e, modulus=2).monoms()
            ):
                found.append((i, j, q))
    print(f"e{k} separators:", found)
