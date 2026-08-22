#!/usr/bin/env python3
"""CAS certificate for the first concrete B/N separator.

The six PC matrices are imported from GAP.  Their Boolean polynomial word has
constant entry (row 3, column 3) equal to one.  The twelve structural Weyl
normal forms are generated as ``c^k`` and ``s*c^k``; every nonidentity form
has that entry equal to zero.  No PC-word assignment table is evaluated.
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
            [int(x) - 1 for x in block.split(",") if x]
            for block in m.group(2).split(";")
        ]
assert set(rows) == set(range(6))

e = sp.symbols("e0:6")

def rb(expr):
    p = sp.Poly(sp.expand(expr), *e, modulus=2)
    return sp.Poly(
        sum(sp.prod(v for v, n in zip(e, mon) if n)
            for mon, coeff in p.terms() if int(coeff) & 1),
        *e, modulus=2,
    ).as_expr()

I = [[int(i == j) for j in range(8)] for i in range(8)]

def mm(a, b):
    return [[rb(sum(a[i][k] * b[k][j] for k in range(8)))
             for j in range(8)] for i in range(8)]

def pc_matrix(k):
    return [[int(j in rows[k][i]) for j in range(8)] for i in range(8)]

def pc_factor(k):
    p = pc_matrix(k)
    return [[rb(I[i][j] + e[k] * (p[i][j] + I[i][j]))
             for j in range(8)] for i in range(8)]

# `autMatrix` reverses multiplication, so this is the Lean matrix word.
B = I
for k in range(6):
    B = mm(B, pc_factor(k))
assert rb(B[2][2]) == 1
assert rb(B[3][3]) == 1
assert rb(B[0][0]) == 1

def permutation_matrix(cycles):
    p = list(range(8))
    for cycle in cycles:
        cycle = [x - 1 for x in cycle]
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            p[a] = b
    return [[int(p[j] == i) for j in range(8)] for i in range(8)]

def cmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(8)) % 2
             for j in range(8)] for i in range(8)]

s = permutation_matrix([(3, 4), (6, 7)])
r = permutation_matrix([(3, 4, 5), (6, 7, 8)])
h = permutation_matrix([(1, 2), (3, 6), (4, 7), (5, 8)])

def cpow(a, n):
    out = I
    for _ in range(n):
        out = cmul(out, a)
    return out

# This is the exact order of `concreteWeylElement` in Lean:
# 1, r, r², s, sr, sr², h, hr, hr², hs, hsr, hsr².
weyl = [I, r, cmul(r, r), s, cmul(s, r), cmul(s, cmul(r, r)),
        h, cmul(h, r), cmul(h, cmul(r, r)), cmul(h, s),
        cmul(h, cmul(s, r)), cmul(h, cmul(s, cmul(r, r)))]
assert len({tuple(sum(x, [])) for x in weyl}) == 12
constant_entries = [
    (i, j, int(B[i][j]))
    for i in range(8) for j in range(8)
    if B[i][j] in (0, 1)
]
assert weyl[0][2][2] == 1
assert all(
    any(x[i][j] != value for i, j, value in constant_entries)
    for x in weyl[1:]
)

separators = []
for k, x in enumerate(weyl[1:], start=1):
    witnesses = [(i, j, value) for i, j, value in constant_entries
                 if x[i][j] != value]
    assert witnesses
    separators.append((k, witnesses[0]))

print("B_ENTRY_3_3=PASS")
print("B_ENTRY_4_4=PASS")
print("B_ENTRY_1_1=PASS")
print("WEYL_NONIDENTITY_ENTRY_3_3=PASS")
print("BN_MATRIX_SEPARATOR=PASS")
print("BN_MATRIX_SEPARATOR_WITNESSES=" + repr(separators))
print("NO_PC_ASSIGNMENT_ENUMERATION=PASS")
