#!/usr/bin/env python3
"""Derive the inverse coordinates for the symbolic PC law over GF(2)."""
import sympy as sp

e = sp.symbols("e0:6")
h = sp.symbols("h0:6")
vars = e + h

def red(x):
    p = sp.Poly(sp.expand(x), *vars, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(vars, mon):
                if power:
                    term *= v
            out += term
    return sp.Poly(out, *vars, modulus=2).as_expr()

def combine(a, b):
    return [
        red(a[0] + b[0]),
        red(a[1] + b[1]),
        red(a[1]*b[0] + a[2] + b[2]),
        red(a[1]*b[0] + a[3] + a[4]*b[0] + b[3]),
        red(a[4] + b[4]),
        red(a[1]*a[2]*b[0] + a[1]*b[0]*b[1] +
            a[1]*b[0]*b[2] + a[1]*b[1] + a[2]*b[0] +
            a[2]*b[2] + a[3]*b[1] + a[4]*b[0]*b[1] +
            a[4]*b[1] + a[4]*b[2] + a[5] + b[5]),
    ]

inv = [
    e[0],
    e[1],
    red(e[1]*e[0] + e[2]),
    red(e[1]*e[0] + e[3] + e[4]*e[0]),
    e[4],
    red(e[1]*e[2]*e[0] + e[1]*e[0]*e[1] +
        e[1]*e[0]*(e[1]*e[0] + e[2]) + e[1]*e[1] +
        e[2]*e[0] + e[2]*(e[1]*e[0] + e[2]) + e[3]*e[1] +
        e[4]*e[0]*e[1] + e[4]*e[1] + e[4]*(e[1]*e[0] + e[2]) + e[5]),
]
assert all(red(x) == 0 for x in combine(e, inv))
print("PC_COMBINE_RIGHT_INVERSE_SYMBOLIC=PASS")
for i, x in enumerate(inv):
    print(f"h{i}={x}")
assert all(red(x) == 0 for x in combine(inv, e))
print("PC_COMBINE_LEFT_INVERSE_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
