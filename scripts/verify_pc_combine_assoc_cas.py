#!/usr/bin/env python3
"""Symbolically verify associativity of the Boolean PC law over GF(2)."""
import sympy as sp

e = sp.symbols("e0:6")
f = sp.symbols("f0:6")
g = sp.symbols("g0:6")
vars = e + f + g

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
    return sp.Poly(sp.expand(out), *vars, modulus=2).as_expr()

def xor(*xs):
    return red(sum(xs))

def and2(a, b):
    return red(a * b)

def combine(a, b, k):
    if k == 0: return xor(a[0], b[0])
    if k == 1: return xor(a[1], b[1])
    if k == 2: return xor(and2(a[1], b[0]), a[2], b[2])
    if k == 3: return xor(and2(a[1], b[0]), a[3], and2(a[4], b[0]), b[3])
    if k == 4: return xor(a[4], b[4])
    return xor(and2(and2(a[1], a[2]), b[0]),
               and2(and2(a[1], b[0]), b[1]),
               and2(and2(a[1], b[0]), b[2]),
               and2(a[1], b[1]), and2(a[2], b[0]),
               and2(a[2], b[2]), and2(a[3], b[1]),
               and2(and2(a[4], b[0]), b[1]),
               and2(a[4], b[1]), and2(a[4], b[2]), a[5], b[5])

lhs = [combine([combine(e, f, j) for j in range(6)], g, k)
       for k in range(6)]
rhs = [combine(e, [combine(f, g, j) for j in range(6)], k)
       for k in range(6)]
assert all(red(a + b) == 0 for a, b in zip(lhs, rhs))
print("PC_COMBINE_ASSOC_SYMBOLIC=PASS")
print("BOOLEAN_IDEMPOTENT_REDUCTION=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
