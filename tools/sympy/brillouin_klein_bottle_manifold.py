#!/usr/bin/env python3
"""Exact-rational Brillouin Klein bottle manifold certificate."""
import sympy as sp

Tx = sp.Matrix([[0, 1], [1, 0]])
Ty = sp.Matrix([[1, 0], [0, -1]])
I = sp.eye(2)
minusI = -I
Txy = Tx * Ty

assert Tx * Tx == I
assert Ty * Ty == I
assert Tx * Ty == -(Ty * Tx)
assert Tx * Ty == minusI * (Ty * Tx)
assert Txy * Txy == minusI

kx, ky = sp.symbols("kx ky")
def glide(p):
    x, y = p
    return (sp.simplify(x + 1), sp.simplify(-y))
def glide_inv(p):
    x, y = p
    return (sp.simplify(x - 1), sp.simplify(-y))
def y_loop(p):
    x, y = p
    return (x, sp.simplify(y + 2))
def y_loop_inv(p):
    x, y = p
    return (x, sp.simplify(y - 2))

p = (kx, ky)
assert glide(glide_inv(p)) == p
assert glide_inv(glide(p)) == p
assert glide(y_loop(glide_inv(p))) == y_loop_inv(p)
assert glide(y_loop(glide_inv(y_loop(p)))) == p

# Z2 invariant stability under even gauge shifts.
g0, gp, n = sp.symbols("g0 gp n", integer=True)
for a in range(-3, 4):
    for b in range(-3, 4):
        for m in range(-3, 4):
            assert ((a + 2*m + b) % 2) == ((a + b) % 2)

print("BRILLOUIN_KLEIN_BOTTLE_MANIFOLD_SYMPY_CERTIFICATE_OK")
