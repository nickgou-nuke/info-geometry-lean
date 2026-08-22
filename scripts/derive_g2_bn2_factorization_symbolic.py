#!/usr/bin/env python3
"""Derive the two symbolic BN2 branches for the concrete PC chart.

The matrix orientation is the repository orientation: a PC word is the
reverse matrix product used by ``autMatrix``.  The Boolean coordinate e1
separates the identity branch from the big cell.  The big-cell witness is the
constant simple-root factor p1 on the right; all remaining coordinates are
recovered symbolically.  No Boolean assignments are enumerated.
"""

import sympy as sp

from verify_pc_collector_symbolic import (
    I, e, factor, gens, invmat, mm, red, recover,
)
from derive_g2_bn2_symbolic import s, M


def pc_word(bits):
    result = I
    for index in range(6):
        result = mm(result, factor(gens[index], bits[index]))
    return result


def pc_word_inverse(bits):
    result = I
    for index in reversed(range(6)):
        result = mm(result, factor(invmat(index), bits[index]))
    return result


def basis(index):
    return [int(k == index) for k in range(6)]


target = mm(mm(s, M), s)

# Identity branch: e1 = 0 makes the conjugate a PC word.
identity_left = recover(target, check=False)
identity_residual = [
    red((target[i][j] - pc_word(identity_left)[i][j]).subs(e[1], 0))
    for i in range(8)
    for j in range(8)
]
if any(identity_residual):
    print("BN2_IDENTITY_BRANCH=FAIL")
    raise SystemExit(1)
print("BN2_IDENTITY_BRANCH=PASS")

# Big-cell branch: the constant simple-root factor p1 is the right witness.
# For target = a*s*p1, solve a = target*p1^-1*s and recover a in B.
right = basis(1)
left_matrix = mm(target, mm(pc_word_inverse(right), s))
left = recover(left_matrix, check=False)
big_residual = [
    red((left_matrix[i][j] - pc_word(left)[i][j]).subs(e[1], 1))
    for i in range(8)
    for j in range(8)
]
if any(big_residual):
    print("BN2_BIG_CELL_SYMBOLIC=FAIL")
    raise SystemExit(1)
print("BN2_BIG_CELL_RIGHT_COORD=1=PASS")
for coordinate, value in enumerate(left):
    print(
        f"  LEFT[{coordinate}]="
        f"{sp.Poly(value.subs(e[1], 1), *e, modulus=2).as_expr()}"
    )
print("BN2_BIG_CELL_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
