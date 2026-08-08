#!/usr/bin/env python3
"""Exact two-sheet chiral operator closure certificate.

Basis order: |+,+>, |+,->, |-,+>, |- ,->.
The outer factor is particle/hole; the inner factor is chiral.
"""
import sympy as sp

Z = sp.zeros(2)
I2 = sp.eye(2)
up2 = sp.Matrix([[0, 1], [0, 0]])
um2 = sp.Matrix([[0, 0], [1, 0]])

def kron(a, b):
    return sp.kronecker_product(a, b)

def comm(a, b):
    return a*b - b*a

def anti(a, b):
    return a*b + b*a

u_plus = kron(up2, I2)
u_minus = kron(um2, I2)
s_plus = kron(I2, up2)
s_minus = kron(I2, um2)
U3 = comm(u_plus, u_minus)
S3 = comm(s_plus, s_minus)
Id = sp.eye(4)
ops = {"u+": u_plus, "u-": u_minus, "s+": s_plus, "s-": s_minus}

assert u_plus*u_plus == sp.zeros(4)
assert u_minus*u_minus == sp.zeros(4)
assert s_plus*s_plus == sp.zeros(4)
assert s_minus*s_minus == sp.zeros(4)
assert anti(u_plus, u_minus) == Id
assert anti(s_plus, s_minus) == Id
assert comm(u_plus, u_minus) == U3
assert comm(s_plus, s_minus) == S3
for a in (u_plus, u_minus):
    for b in (s_plus, s_minus):
        assert comm(a, b) == sp.zeros(4)

# Mixed products are the four grade-two/zero tensor channels.
channels = {
    "q++": u_plus*s_plus,
    "q+-": u_plus*s_minus,
    "q-+": u_minus*s_plus,
    "q--": u_minus*s_minus,
}
assert all(q != sp.zeros(4) for q in channels.values())
assert len({tuple(q) for q in channels.values()}) == 4

# The generated associative algebra is all M4: the flattened generators,
# their products, and the identity span all 16 matrix units.
span_candidates = [Id, U3, S3, u_plus, u_minus, s_plus, s_minus]
span_candidates += list(channels.values())
span_matrix = sp.Matrix.hstack(*[sp.Matrix(a).reshape(16, 1) for a in span_candidates])
assert span_matrix.rank() == 11
# Closing under multiplication once more supplies the full 16-dimensional span.
span_candidates += [a*b for a in span_candidates for b in span_candidates]
span_matrix = sp.Matrix.hstack(*[sp.Matrix(a).reshape(16, 1) for a in span_candidates])
assert span_matrix.rank() == 16

# Möbius/parity involutions on a scalar coordinate z.
def mobius_parity(z):
    return -z

def mobius_particle_hole(z):
    return 1/z

def mobius_combined(z):
    return -1/z

z = sp.Symbol('z', nonzero=True)
assert mobius_parity(mobius_parity(z)) == z
assert mobius_particle_hole(mobius_particle_hole(z)) == z
assert mobius_combined(mobius_combined(z)) == z

print("PASS two-sheet chiral closure")
print("dimension=16; generated_algebra_rank=16")
print("nilpotent_squares=4; CAR_pairs=2; cross_commutators=4_zero")
print("U3=diag(1,1,-1,-1); S3=diag(1,-1,1,-1)")
print("mixed_channels=4; mobius_involutions=3")
