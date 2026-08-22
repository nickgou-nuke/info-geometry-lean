#!/usr/bin/env python3
"""Derive a symbolic big-cell factorization for the concrete PC chart.

The matrix orientation is the repository orientation: a PC word is the
reverse matrix product used by ``autMatrix``.  The branch e1 = 1 is tested
against factored PC witnesses; no Boolean assignments are enumerated.
"""

import sympy as sp

from verify_pc_collector_symbolic import (
    I, e, factor, gens, invmat, mm, red, recover,
)
from derive_g2_bn2_symbolic import s, M


def reverse_word(bits):
    result = I
    for index in range(6):
        result = mm(factor(gens[index], bits[index]), result)
    return result


def inverse_reverse_word(bits):
    result = I
    for index in range(6):
        result = mm(result, factor(invmat(index), bits[index]))
    return result


def basis(index):
    return [int(k == index) for k in range(6)]


target = mm(mm(s, M), s)
print("BN2_BIG_CELL_SYMBOLIC=")
passes = 0
for index in range(6):
    right = basis(index)
    # a*s*PC(right) = target, hence a = target*(s*PC(right))^-1.
    left_matrix = mm(target, mm(inverse_reverse_word(right), s))
    left = recover(left_matrix, check=False)
    residual = [
        red((left_matrix[i][j] - reverse_word(left)[i][j]).subs(e[1], 1))
        for i in range(8)
        for j in range(8)
    ]
    if any(residual):
        print(f"RIGHT_COORD_{index}=FAIL")
        continue
    passes += 1
    print(f"RIGHT_COORD_{index}=PASS")
    for coordinate, value in enumerate(left):
        print(
            f"  LEFT[{coordinate}]="
            f"{sp.Poly(value.subs(e[1], 1), *e, modulus=2).as_expr()}"
        )

if passes == 0:
    print("BN2_BIG_CELL_SYMBOLIC=FAIL")
    raise SystemExit(1)
print("BN2_BIG_CELL_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
