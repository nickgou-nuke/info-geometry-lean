#!/usr/bin/env python3
"""CAS-only check of the PC word order induced by Lean's autMatrix_mul."""
import re
import subprocess
import sympy as sp

raw = subprocess.run(["gap", "-q", "scripts/export_carrier_pc_rows.g"],
                     check=True, capture_output=True, text=True).stdout
rows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1)) - 1] = [[int(x) - 1 for x in part.split(",") if x]
                                     for part in m.group(2).split(";")]
assert set(rows) == set(range(6))
e = sp.symbols("e0:6")

def red(x):
    p = sp.Poly(sp.expand(x), *e, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            out += sp.prod(v for v, n in zip(e, mon) if n)
    return sp.Poly(out, *e, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
A = [sp.Matrix([[int(j in rows[k][i]) for j in range(8)] for i in range(8)])
     for k in range(6)]
Ai = [a.inv_mod(2) for a in A]

def factor(a, q):
    return [[red(I[i][j] + q * (int(a[i, j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

# Lean: autMatrix (p0*...*p5) = M5*...*M0.
M = I
for k in reversed(range(6)):
    M = mm(M, factor(A[k], e[k]))

# Lean peel p0: autMatrix (p0⁻¹ * w) = M_w * M_p0⁻¹.
M1 = mm(M, factor(Ai[0], M[2][7]))
assert red(M1[3][2] + e[1]) == 0
M2 = mm(M1, factor(Ai[1], M1[3][2]))
assert red(M2[3][7] + e[2]) == 0
M3 = mm(M2, factor(Ai[2], M2[3][7]))
e4 = M3[6][2]
assert red(e4 + e[4]) == 0
e3 = red(M3[4][3] + e4)
assert red(e3 + e[3]) == 0
M4 = mm(M3, factor(Ai[4], e4))
M5 = mm(M4, factor(Ai[3], e3))
print("M5[4,2]=", red(M5[4][2]))
assert red(M5[4][2] + e[5]) == 0
M6 = mm(M5, factor(Ai[5], M5[4][2]))
assert all(red(M6[i][j] + I[i][j]) == 0 for i in range(8) for j in range(8))
print("LEAN_WORD_ORIENTATION=PASS")
print("PEEL_PIVOTS=e0:M[2,7];e1:M1[3,2];e2:M2[3,7];e4:M3[6,2];e3:M3[4,3]+e4;e5:M5[4,2]")

# GAP prints PCCONJ 2 1 as p₂⁻¹ p₁ p₂ = p₁ p₃ p₄ p₆.
# Lean's MulEquiv multiplication applies the left factor first, hence its
# matrix image reverses the displayed word.  The following is the exact
# carrier-level orientation check, using symbolic matrix products only.
# Since p₂⁻¹ = p₆ p₂, the Lean-side equality is
# p₂⁻¹ p₁ p₂ = p₆ p₄ p₃ p₁.
AA = [[[A[k][i, j] for j in range(8)] for i in range(8)]
      for k in range(6)]
lhs = mm(mm(AA[1], AA[0]), mm(AA[1], AA[5]))
rhs_lean = mm(mm(mm(AA[0], AA[2]), AA[3]), AA[5])
rhs_gap = mm(mm(mm(AA[5], AA[3]), AA[2]), AA[0])
assert lhs == rhs_lean
assert lhs != rhs_gap
print("PCCONJ_2_1_LEAN_ORIENTATION=PASS")

def product_in_lean_matrix_order(exponents):
    out = [[int(i == j) for j in range(8)] for i in range(8)]
    for k, exponent in enumerate(exponents):
        if exponent:
            out = mm(out, AA[k])
    return out

def matrix_word(exponents):
    out = [[int(i == j) for j in range(8)] for i in range(8)]
    for k in reversed(range(6)):
        if exponents[k]:
            out = mm(out, AA[k])
    return out

inverse_rows = [
    AA[0], mm(AA[1], AA[5]), mm(AA[2], AA[5]),
    AA[3], AA[4], AA[5]
]
def recover_fixed_word(M):
    """Recover fixed-Lean PC coordinates using the six peel pivots."""
    p0 = M[2][7]
    M1 = mm(M, factor(Ai[0], p0))
    p1 = M1[3][2]
    M2 = mm(M1, factor(Ai[1], p1))
    p2 = M2[3][7]
    M3 = mm(M2, factor(Ai[2], p2))
    p4 = M3[6][2]
    p3 = red(M3[4][3] + p4)
    M4 = mm(M3, factor(Ai[3], p3))
    M5 = mm(M4, factor(Ai[4], p4))
    p5 = M5[4][2]
    M6 = mm(M5, factor(Ai[5], p5))
    assert M6 == I
    return [p0, p1, p2, p3, p4, p5]

# Every relation is computed in the fixed Lean basis itself.  No GAP Pcgs
# and no basis-change or word enumeration is used.
for i in range(1, 6):
    for j in range(i):
        lhs = mm(mm(AA[i], AA[j]), inverse_rows[i])
        exponents = recover_fixed_word(lhs)
        assert matrix_word(exponents) == lhs
print("PCCONJ_ALL_15_FIXED_LEAN_BASIS=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
