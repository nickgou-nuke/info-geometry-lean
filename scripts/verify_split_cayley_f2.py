#!/usr/bin/env python3
"""Independent finite check of the split Cayley Zorn law over F_2.

The formulas are those of Lopatin--Zubkov, arXiv:2208.08122v3, §1.2.
This script is evidence only; Lean remains the proof authority.
"""

from itertools import product

F = range(2)
V = list(product(F, repeat=3))
O = list(product(F, V, V, F))

def addv(x, y): return tuple((a + b) % 2 for a, b in zip(x, y))
def dot(x, y): return sum(a*b for a, b in zip(x, y)) % 2
def cross(x, y):
    return ((x[1]*y[2] + x[2]*y[1]) % 2,
            (x[2]*y[0] + x[0]*y[2]) % 2,
            (x[0]*y[1] + x[1]*y[0]) % 2)
def mul(a, b):
    aa, u, v, bb = a
    cc, x, y, dd = b
    return ((aa*cc + dot(u, y)) % 2,
            addv(tuple((aa*z) % 2 for z in x),
                 addv(tuple((dd*z) % 2 for z in u), cross(v, y))),
            addv(tuple((cc*z) % 2 for z in v),
                 addv(tuple((bb*z) % 2 for z in y), cross(u, x))),
            (dot(v, x) + bb*dd) % 2)
def norm(a):
    aa, u, v, bb = a
    return (aa*bb + dot(u, v)) % 2

def delta1(r, x):
    aa, u, v, bb = x
    rv = dot(r, v)
    return ((aa-rv) % 2,
            tuple(((aa-bb-rv)*r[i] + u[i]) % 2 for i in range(3)),
            tuple((v[i] - cross(u, r)[i]) % 2 for i in range(3)),
            (bb+rv) % 2)

def delta2(r, x):
    aa, u, v, bb = x
    ur = dot(u, r)
    return ((aa+ur) % 2,
            tuple((u[i] + cross(v, r)[i]) % 2 for i in range(3)),
            tuple(((-aa+bb-ur)*r[i] + v[i]) % 2 for i in range(3)),
            (bb-ur) % 2)

assert len(O) == 256
for a in O:
    for b in O:
        assert norm(mul(a, b)) == norm(a)*norm(b) % 2
print("PASS: split Cayley Zorn norm composition over F2 (65536 products)")

one = (1, (0,0,0), (0,0,0), 1)
for a in O:
    assert mul(one, a) == a and mul(a, one) == a
print("PASS: two-sided unit")

for r in V:
    for x in O:
        for y in O:
            assert delta1(r, mul(x, y)) == mul(delta1(r, x), delta1(r, y))
            assert delta2(r, mul(x, y)) == mul(delta2(r, x), delta2(r, y))
print("PASS: delta1 and delta2 preserve Zorn multiplication")
