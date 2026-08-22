#!/usr/bin/env python3
"""CAS-first verification of the six PC collector identities.

The exponents are Boolean indeterminates.  All matrix products and peeling
are performed in GF(2)[e0,...,e5,c] with idempotent Boolean reduction; no
assignment enumeration is used.
"""
import re
import subprocess
import sympy as sp

raw = subprocess.run(
    ["gap", "-q", "scripts/export_carrier_pc_rows.g"],
    check=True, capture_output=True, text=True).stdout
rows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")
c = sp.symbols("c")
vars_ = e + (c,)

def red(x):
    p = sp.Poly(sp.expand(x), *vars_, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(vars_, mon):
                if power:
                    term *= v
            out += term
    return sp.Poly(out, *vars_, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
gens = [[[int(j in rows[k][i]) for j in range(8)] for i in range(8)]
        for k in range(6)]

def invmat(k):
    if k in (0, 3, 4, 5):
        return gens[k]
    return mm(gens[5], gens[k])

def factor(a, q):
    return [[red(I[i][j] + q * (int(a[i][j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

def word(bits):
    out = I
    for k in range(6):
        out = mm(out, factor(gens[k], bits[k]))
    return out

def peel(M, k, pivot):
    return mm(factor(invmat(k), pivot), M)

def recover(M, check=True):
    p0 = M[2][7]
    M1 = peel(M, 0, p0)
    p1 = M1[3][2]
    M2 = peel(M1, 1, p1)
    p2 = M2[3][7]
    M3 = peel(M2, 2, p2)
    p4 = M3[6][2]
    p3 = red(M3[4][3] + p4)
    M4 = peel(M3, 3, p3)
    M5 = peel(M4, 4, p4)
    p5 = M5[4][2]
    M6 = peel(M5, 5, p5)
    if check:
        assert all(red(M6[i][j] - I[i][j]) == 0
                   for i in range(8) for j in range(8))
    return [p0, p1, p2, p3, p4, p5]

def combine(a, b):
    return [
        red(a[0] + b[0]),
        red(a[1] + b[1]),
        red(a[1]*b[0] + a[2] + b[2]),
        red(a[1]*b[0] + a[3] + a[4]*b[0] + b[3]),
        red(a[4] + b[4]),
        red(a[1]*a[2]*b[0] + a[1]*b[0]*b[1] +
            a[1]*b[0]*b[2] + a[1]*b[1] + a[2]*b[0] +
            a[2]*b[2] + a[3]*b[1] + a[4]*b[0]*b[1] +
            a[4]*b[1] + a[4]*b[2] + a[5] + b[5]),
    ]

lhs = word(e)
for j in range(6):
    rhs = word([int(k == j) * c for k in range(6)])
    actual = recover(mm(lhs, rhs), check=False)
    expected = combine(e, [int(k == j) * c for k in range(6)])
    ok = all(red(x - y) == 0 for x, y in zip(actual, expected))
    if not ok:
        print("FAIL j", j)
        print("actual", actual)
        print("expected", expected)
    assert ok
    print(f"COLLECTOR j={j}: PASS")
    print("  " + ", ".join(f"g{k}={sp.Poly(x, *vars_, modulus=2).as_expr()}"
                            for k, x in enumerate(actual)))

print("PC_COLLECTOR_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
