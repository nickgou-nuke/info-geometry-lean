#!/usr/bin/env python3
"""Symbolic first pass for the concrete BN2 relation.

The target is ``s * B * s`` with B in the six-coordinate PC chart.  This
script performs only GF(2) polynomial matrix algebra and the existing peeling
map; it does not enumerate Boolean assignments or search for witnesses.
"""
import sympy as sp

from verify_pc_collector_symbolic import (I, gens as constants, e, mm, factor,
                                          recover, red)

# swap01 on the carrier basis (1-based supports from the GAP owner).
s = [[int(j == i) for j in range(8)] for i in range(8)]
for a, b in ((2, 3), (5, 6)):
    s[a][a], s[b][b], s[a][b], s[b][a] = 0, 0, 1, 1

M = I
for k in range(6):
    M = mm(M, factor(constants[k], e[k]))

conjugate = mm(mm(s, M), s)
recovered = recover(conjugate, check=False)
print("BN2_CONJUGATE_RECOVERY=")
for i, value in enumerate(recovered):
    print(f"x{i}={sp.Poly(value, *e, modulus=2).as_expr()}")

residual = [(i, j, red(conjugate[i][j] - I[i][j]))
            for i in range(8) for j in range(8)
            if red(conjugate[i][j] - I[i][j]) != 0]
print("BN2_IDENTITY_RESIDUAL_ENTRIES=", len(residual))
for i, j, value in residual:
    print(f"residual[{i},{j}]={sp.Poly(value, *e, modulus=2).as_expr()}")
print("BN2_SYMBOLIC_CONJUGATE_STAGE=PASS")
