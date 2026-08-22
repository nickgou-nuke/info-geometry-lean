#!/usr/bin/env python3
"""Derive the PC product law in Lean's reversed autMatrix convention.

The generator rows come directly from GAP.  This is symbolic GF(2)
polynomial arithmetic; no assignments or word enumeration are used.
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
vars = e + f

def red(x):
    p = sp.Poly(sp.expand(x), *vars, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, n in zip(vars, mon):
                if n:
                    term *= v
            out += term
    return sp.Poly(out, *vars, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
gens = [[[int(j in rows[k][i]) for j in range(8)] for i in range(8)]
        for k in range(6)]

def inv(k):
    if k in (0, 3, 4, 5):
        return gens[k]
    return mm(gens[k], gens[5])

def factor(k, bit):
    return [[red(I[i][j] + bit * (gens[k][i][j] + I[i][j]))
             for j in range(8)] for i in range(8)]

def factor_inv(k, bit):
    ik = inv(k)
    return [[red(I[i][j] + bit * (ik[i][j] + I[i][j]))
             for j in range(8)] for i in range(8)]

for k in range(6):
    assert mm(gens[k], inv(k)) == I
    assert mm(inv(k), gens[k]) == I
    assert mm(factor(k, e[k]), factor_inv(k, e[k])) == I
    assert mm(factor_inv(k, e[k]), factor(k, e[k])) == I

def word(bits):
    out = I
    for k in reversed(range(6)):
        out = mm(out, factor(k, bits[k]))
    return out

def peel(M, k, bit):
    return mm(M, factor_inv(k, bit))

# Group product f * e in matrix form is M_f M_e.
M = mm(word(f), word(e))
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
assert all(red(M6[i][j] + I[i][j]) == 0
           for i in range(8) for j in range(8))
print("LEAN_PC_NORMAL_FORM_SYMBOLIC=PASS")
derived_product = [p0, p1, p2, p3, p4, p5]
for k, bit in enumerate(derived_product):
    assert mm(factor(k, bit), factor_inv(k, bit)) == I
    assert mm(factor_inv(k, bit), factor(k, bit)) == I
reconstructed = word(derived_product)
if not all(red(M[i][j] + reconstructed[i][j]) == 0
           for i in range(8) for j in range(8)):
    print("LEAN_PC_RECONSTRUCTION=FAIL")
    for i in range(8):
        for j in range(8):
            d = red(M[i][j] + reconstructed[i][j])
            if d != 0:
                print("mismatch", i, j, d)
                raise SystemExit(1)
print("LEAN_PC_CONCRETE_PRODUCT_EQUALS_PCCOMBINE=PASS")
for name, value in (("g0", p0), ("g1", p1), ("g2", p2),
                    ("g3", p3), ("g4", p4), ("g5", p5)):
    print(f"{name}={sp.Poly(value, *vars, modulus=2).as_expr()}")
print("NO_ASSIGNMENT_ENUMERATION=PASS")

# In Lean order, the inverse matrix is A₀⁻¹ A₁⁻¹ ... A₅⁻¹.
Minv = I
for k in range(6):
    Minv = mm(Minv, factor_inv(k, e[k]))
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
assert all(red(N6[i][j] + I[i][j]) == 0
           for i in range(8) for j in range(8))
print("LEAN_PC_INVERSE_NORMAL_FORM_SYMBOLIC=PASS")
for name, value in (("q0", q0), ("q1", q1), ("q2", q2),
                    ("q3", q3), ("q4", q4), ("q5", q5)):
    print(f"{name}={sp.Poly(value, *e, modulus=2).as_expr()}")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
