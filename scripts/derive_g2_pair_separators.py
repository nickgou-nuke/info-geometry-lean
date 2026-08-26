#!/usr/bin/env python3
"""Derive constant matrix-entry witnesses for all distinct G2 Weyl pairs."""

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
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

vars = sp.symbols("d0:6 e0:6")

def rb(expr):
    p = sp.Poly(sp.expand(expr), *vars, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, n in zip(vars, mon):
                if n:
                    term *= v ** n
            out += term
    return sp.Poly(out, *vars, modulus=2).as_expr()

def evaluates_to(poly, assignment):
    value = 0
    for mon, coeff in poly.terms():
        if int(coeff) & 1:
            mask = sum((1 << n) for n, exponent in enumerate(mon) if exponent)
            if assignment & mask == mask:
                value ^= 1
    return value

I = [[int(i == j) for j in range(8)] for i in range(8)]

def mm(a, b):
    return [[rb(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

def perm(mapping):
    return [[int(mapping[i] == j) for j in range(8)] for i in range(8)]

cycle = perm([0, 1, 3, 4, 2, 6, 7, 5])
cartan = perm([1, 0, 5, 6, 7, 2, 3, 4])
swap = perm([0, 1, 3, 2, 4, 6, 5, 7])
c = mm(cycle, cartan)

def mpow(a, n):
    out = I
    for _ in range(n):
        out = mm(out, a)
    return out

weyl = []
for b in (False, True):
    for p in (0, 5, 4, 3, 2, 1):
        weyl.append(mm(mpow(c, p), swap) if b else mpow(c, p))

def factor(k, offset):
    p = [[int(j in rows[k][i]) for j in range(8)] for i in range(8)]
    x = vars[offset + k]
    return [[rb(I[i][j] + x * (p[i][j] + I[i][j]))
             for j in range(8)] for i in range(8)]

def word(offset):
    out = I
    # Lean's anti-hom image is built by prepending the next PC factor:
    # C₅ · C₄ · ... · C₀.  This mirrors the Lean left-action construction
    # directly; it is not the GAP right-accumulation convention.
    for k in range(6):
        out = mm(factor(k, offset), out)
    return out

left = [word(0), word(6)]
left_weyl = [mm(mm(left[0], w), left[1]) for w in weyl]
for k in range(12):
    for l in range(12):
        if k == l:
            continue
        candidate = None
        for i in range(8):
            for j in range(8):
                poly = sp.Poly(left_weyl[k][i][j],
                               *vars, modulus=2)
                other = int(weyl[l][i][j])
                if all(evaluates_to(poly, assignment) != other
                       for assignment in range(1 << 12)):
                    candidate = (i, j, other)
                    break
            if candidate:
                break
        if candidate is None:
            raise RuntimeError(f"no constant entry witness for pair {k},{l}")
        print(f"PAIR_SEPARATOR {k} {l} {candidate[0]} {candidate[1]} {candidate[2]}")

print("PAIR_SEPARATOR_COUNT=66")
