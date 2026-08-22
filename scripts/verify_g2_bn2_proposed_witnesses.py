#!/usr/bin/env python3
"""Symbolically test the proposed constant-left BN2 witness formulas."""
import sympy as sp

from verify_pc_collector_symbolic import I, e, factor, gens, mm, red, combine
from derive_g2_bn2_symbolic import s, M


def word(bits):
    out = I
    for k in range(6):
        out = mm(out, factor(gens[k], bits[k]))
    return out


def test_chart(name, target, left, right, active):
    equations = []
    rhs = mm(mm(word(left), s), word(right))
    for i in range(8):
        for j in range(8):
            equations.append(red((target[i][j] - rhs[i][j]).subs(active, 1)))
    ok = all(value == 0 for value in equations)
    print(f"{name}={'PASS' if ok else 'FAIL'}")
    if not ok:
        first = next(value for value in equations if value != 0)
        print("  FIRST_RESIDUAL=", sp.Poly(first, *e, modulus=2).as_expr())
    return ok


# Proposed s1 chart: active e0, complement permutation
target_s1 = mm(mm(s, word(e)), s)
left_s1 = [1, 0, 0, 0, 0, 0]
right_s1 = [1, e[4], e[3], e[2], e[1], e[5]]
ok1 = test_chart("PROPOSED_S1_CHART", target_s1, left_s1, right_s1, e[0])

# Proposed s2 chart: active e1, with b = combine(basis(1), sigma2(e)).
c = sp.symbols("dummy")
sigma2 = [e[2], 0, e[0], e[3], e[5], e[4]]
basis1 = [0, 1, 0, 0, 0, 0]
right_s2 = [combine(basis1, sigma2)[k] for k in range(6)]
t = mm(s, mm(s, M))
target_s2 = mm(mm(t, word(e)), t)
left_s2 = basis1
ok2 = test_chart("PROPOSED_S2_CHART", target_s2, left_s2, right_s2, e[1])

if not (ok1 and ok2):
    raise SystemExit(1)
print("BN2_PROPOSED_WITNESSES_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
