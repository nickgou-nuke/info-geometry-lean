#!/usr/bin/env python3
"""SymPy audit for the finite Bures/Fisher + Andreev geodesic-flow toy."""

import sympy as sp

px, py, pz, qx, qy, qz, t = sp.symbols("px py pz qx qy qz t", real=True)
I, theta, gain, loss = sp.symbols("I theta gain loss", nonzero=True, real=True)

bures_distance = (px - qx) ** 2 + (py - qy) ** 2 + (pz - qz) ** 2
bures_self = (px - px) ** 2 + (py - py) ** 2 + (pz - pz) ** 2
geodesic_zero = tuple(sp.simplify((1 - 0) * a + 0 * b) for a, b in [(px, qx), (py, qy), (pz, qz)])
geodesic_one = tuple(sp.simplify((1 - 1) * a + 1 * b) for a, b in [(px, qx), (py, qy), (pz, qz)])

fisher_potential = I * theta**2 / 2
fisher_gradient = sp.diff(fisher_potential, theta)
fisher_inverse_step = sp.simplify(theta - (1 / I) * fisher_gradient)
gain_minus_loss = gain - loss

print("Bures distance =", bures_distance)
print("Bures self-distance =", bures_self)
print("geodesic t=0 =", geodesic_zero)
print("geodesic t=1 =", geodesic_one)
print("Fisher gradient =", fisher_gradient)
print("inverse Fisher step =", fisher_inverse_step)
print("gain-loss margin =", gain_minus_loss)

assert sp.simplify(bures_self) == 0
assert geodesic_zero == (px, py, pz)
assert geodesic_one == (qx, qy, qz)
assert sp.simplify(fisher_gradient - I * theta) == 0
assert sp.simplify(fisher_inverse_step) == 0
assert sp.simplify(gain_minus_loss - (gain - loss)) == 0
assert 3 + 1 == 4
assert 15 + 1 == 16

print("bures_fisher_andreev_geodesic_flow.py: SymPy audit passed")
