#!/usr/bin/env python3
"""Symbolic associativity certificate for the PC coordinate law.

The Boolean formula is reduced in GF(2) with x^2=x.  This is a symbolic
polynomial identity; no Boolean assignment or word enumeration is used.
"""
import sympy as sp

e = sp.symbols("e0:6")
f = sp.symbols("f0:6")
g = sp.symbols("g0:6")
variables = e + f + g

def red(x):
    p = sp.Poly(sp.expand(x), *variables, modulus=2)
    out = 0
    for mon, coeff in p.terms():
        if int(coeff) & 1:
            term = 1
            for v, power in zip(variables, mon):
                if power:
                    term *= v
            out += term
    return sp.Poly(out, *variables, modulus=2).as_expr()

def combine(a, b):
    return [
        red(a[0] + b[0]),
        red(a[1] + b[1]),
        red(a[1]*b[0] + a[2] + b[2]),
        red(a[1]*b[0] + a[3] + a[4]*b[0] + b[3]),
        red(a[4] + b[4]),
        red(a[1]*a[2]*b[0] + a[1]*b[0]*b[1] +
            a[1]*b[0]*b[2] + a[1]*b[0] + a[1]*b[1] +
            a[2]*b[0] + a[2]*b[2] + a[3]*b[1] +
            a[4]*b[0]*b[1] + a[4]*b[1] + a[4]*b[2] +
            a[5] + b[5]),
    ]

left = combine(combine(e, f), g)
right = combine(e, combine(f, g))
assert all(red(x - y) == 0 for x, y in zip(left, right))
print("PC_COMBINE_ASSOCIATIVE_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
