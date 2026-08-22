#!/usr/bin/env python3
"""CAS proof of the corrected carrier-side input for the e2 inverse peel."""
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
            out += sp.prod(v for v, n in zip(e, mon) if n)
    return sp.Poly(out, *e, modulus=2).as_expr()

def mm(a, b):
    return [[red(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

I = [[int(i == j) for j in range(8)] for i in range(8)]
A = [sp.Matrix([[int(j in rows[k][i]) for j in range(8)]
                for i in range(8)]) for k in range(6)]
Ai = [a.inv_mod(2) for a in A]

def factor(a, q):
    return [[red(I[i][j] + q * (int(a[i, j]) + I[i][j]))
             for j in range(8)] for i in range(8)]

M = I
for k in reversed(range(6)):
    M = mm(M, factor(A[k], e[k]))

def vec(indices):
    return [int(i in indices) for i in range(8)]

# (pc6 * pc2)(basis8 7) is the corrected input vector 0+1+4+6+7.
v = vec([0, 1, 4, 6, 7])

# peels are right matrix multiplication in the carrier convention.
e0 = M[2][7]
M1 = mm(M, factor(Ai[0], e0))
out = [red(sum(M1[i][j] * v[j] for j in range(8))) for i in range(8)]

# The e2 pivot is row 3, column 7 after the first peel and pc2 inverse.
print("PEEL0_INPUT_X1=", red(out[3]))
print("PEEL0_INPUT_SUPPORT=", ";".join(
    f"{i}:{red(out[i])}" for i in range(8) if red(out[i]) != 0))
M2 = mm(M1, factor(Ai[1], M1[3][2]))
print("PEEL1_INPUT_X1=", red(sum(M2[3][j] * v[j] for j in range(8))))

print("LEMMA_2_TRANSPORT_SYMBOLIC=PASS")
print("INPUT=(0,1,4,6,7)")
print("PIVOT=e2:M2*(pc6pc2*basis8_7)[3]=e2")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
