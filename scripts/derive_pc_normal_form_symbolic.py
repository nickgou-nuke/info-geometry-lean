#!/usr/bin/env python3
"""Derive the PC normal-form product symbolically over GF(2).

The GAP rows are the only generator input.  Exponents are Boolean
indeterminates; reduction uses e^2=e and f^2=f.  No word enumeration is used.
"""
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
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")
f = sp.symbols("f0:6")
all_vars = e + f

def red(x):
    p = sp.Poly(sp.expand(x), *all_vars, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(all_vars, mon):
                if power:
                    term *= v
            out += term
    return sp.Poly(out, *all_vars, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
gens = [
    [[int(j in rows[k][i]) for j in range(8)] for i in range(8)]
    for k in range(6)]

def inverse(a):
    # The GAP PC relations give p1,p4,p5,p6 involutive and p2^-1=p6*p2,
    # p3^-1=p6*p3.  This is symbolic matrix algebra, not enumeration.
    if a is gens[0] or a is gens[3] or a is gens[4] or a is gens[5]:
        return a
    return mm(gens[5], a)

def factor(a, q):
    return [[red(I[i][j] + q * (int(a[i][j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

def word(bits):
    out = I
    for k in range(6):
        out = mm(out, factor(gens[k], bits[k]))
    return out

def peel(M, k, pivot):
    return mm(factor(inverse(gens[k]), pivot), M)

def pc_combine(e, f):
    return [
        red(e[0] + f[0]),
        red(e[1] + f[1]),
        red(e[1]*f[0] + e[2] + f[2]),
        red(e[1]*f[0] + e[3] + e[4]*f[0] + f[3]),
        red(e[4] + f[4]),
        red(e[1]*e[2]*f[0] + e[1]*f[0]*f[1] +
            e[1]*f[0]*f[2] + e[1]*f[1] + e[2]*f[0] +
            e[2]*f[2] + e[3]*f[1] + e[4]*f[0]*f[1] +
            e[4]*f[1] + e[4]*f[2] + e[5] + f[5]),
    ]

M = mm(word(e), word(f))
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

assert all(red(M6[i][j] - I[i][j]) == 0 for i in range(8) for j in range(8))
print("PC_NORMAL_FORM_SYMBOLIC=PASS")
for name, value in (("g0", p0), ("g1", p1), ("g2", p2),
                    ("g3", p3), ("g4", p4), ("g5", p5)):
    print(f"{name}={sp.Poly(value, *all_vars, modulus=2).as_expr()}")
derived_product = [p0, p1, p2, p3, p4, p5]
assert all(red(lhs - rhs) == 0
           for lhs, rhs in zip(derived_product, pc_combine(e, f)))
print("PC_CONCRETE_PRODUCT_EQUALS_PCCOMBINE=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")

# Inversion is derived symbolically from (p₀ᵉ⁰⋯p₅ᵉ⁵)⁻¹
# = p₅⁻ᵉ⁵⋯p₀⁻ᵉ⁰, using the same triangular peel.  This is a
# polynomial calculation over GF(2), not a finite word enumeration.
Minv = I
for k in reversed(range(6)):
    Minv = mm(Minv, factor(inverse(gens[k]), e[k]))
q0 = Minv[2][7]
N1 = peel(Minv, 0, q0)
q1 = N1[3][2]
N2 = peel(N1, 1, q1)
q2 = N2[3][7]
N3 = peel(N2, 2, q2)
q4 = N3[6][2]
q3 = red(N3[4][3] + q4)
N4 = peel(N3, 3, q3)
N5 = peel(N4, 4, q4)
q5 = N5[4][2]
N6 = peel(N5, 5, q5)
assert all(red(N6[i][j] - I[i][j]) == 0
           for i in range(8) for j in range(8))
print("PC_INVERSE_NORMAL_FORM_SYMBOLIC=PASS")
for name, value in (("q0", q0), ("q1", q1), ("q2", q2),
                    ("q3", q3), ("q4", q4), ("q5", q5)):
    print(f"{name}={sp.Poly(value, *e, modulus=2).as_expr()}")
derived_inverse = [q0, q1, q2, q3, q4, q5]
pc_inverse = [
    e[0], e[1],
    red(e[0]*e[1] + e[2]),
    red(e[0]*e[1] + e[0]*e[4] + e[3]),
    e[4],
    red(e[0]*e[1]*e[2] + e[0]*e[2] + e[1]*e[3] +
        e[1]*e[4] + e[1] + e[2]*e[4] + e[2] + e[5]),
]
assert all(red(lhs - rhs) == 0
           for lhs, rhs in zip(derived_inverse, pc_inverse))
print("PC_CONCRETE_INVERSE_EQUALS_PCINVERSE=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
