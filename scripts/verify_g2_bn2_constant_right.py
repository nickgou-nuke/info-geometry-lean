#!/usr/bin/env python3
"""CAS gate for the proposed constant-right BN2 chart.

Checks the carrier identity symbolically, without Boolean assignment
enumeration, using ``b = p0`` and recovering the left factor from
``s * B(e) * s * p0 * s``.
"""
import sympy as sp

from verify_pc_collector_symbolic import I, gens, e, factor, mm, recover, red

s = [[int(j == i) for j in range(8)] for i in range(8)]
for a, b in ((2, 3), (5, 6)):
    s[a][a], s[b][b], s[a][b], s[b][a] = 0, 0, 1, 1

M = I
for k in range(6):
    M = mm(M, factor(gens[k], e[k]))
target = mm(mm(s, M), s)

passed = False
for j, p, branch in ((0, gens[0], {e[0]: 1}), (1, gens[1], {e[1]: 1})):
    # If target = A*s*p, then A = target*p⁻¹*s.
    pinv = sp.Matrix(p).inv_mod(2).tolist()
    candidate = [[sp.expand(x).subs(branch) for x in row]
                 for row in mm(mm(target, pinv), s)]
    a = recover(candidate, check=False)
    rhs = I
    for k in range(6):
        rhs = mm(rhs, factor(gens[k], a[k]))
    rhs = mm(mm(rhs, s), p)
    target_branch = [[sp.expand(x).subs(branch) for x in row] for row in target]
    residual = [
        (i, k, sp.Poly(red(target_branch[i][k] - rhs[i][k]), *e, modulus=2).as_expr())
        for i in range(8) for k in range(8)
        if red(target[i][k] - rhs[i][k]) != 0
    ]
    print(f"CONSTANT_RIGHT_P{j}_RESIDUAL_ENTRIES={len(residual)}")
    for i, k, value in residual[:3]:
        print(f"p{j}_residual[{i},{k}]={value}")
    passed |= not residual
if passed:
    print("BN2_CONSTANT_RIGHT=PASS")
else:
    print("BN2_CONSTANT_RIGHT=FAIL")
    raise SystemExit(1)
