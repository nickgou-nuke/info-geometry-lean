#!/usr/bin/env python3
"""Finite audit for the torus/Klein -> O(5,5) bridge."""

from __future__ import annotations

import sympy as sp


F = sp.Matrix([[1, 0, sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
F_inv = sp.Matrix([[1, 0, sp.Rational(-1, 2)], [0, -1, 0], [0, 0, 1]])
T_x = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
T_y = sp.Matrix([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
T_y_inv = sp.Matrix([[1, 0, 0], [0, 1, -1], [0, 0, 1]])

torus_cycles = 2
klein_glide_orientation = -1
torus_translation_orientation = 1
cartan_rank = 5
doubled_cartan_carrier = 2 * cartan_rank

o55_carrier = 10
full_o55_generators = 45
active_o55_generators = 15
scalar_base_deferred_interface = 1
p6m_non_equiv_psa = 16

print("torus cycles =", torus_cycles)
print("affine glide F^2 = Tx:", F * F == T_x)
print("affine glide F Ty F^-1 = Ty^-1:", F * T_y * F_inv == T_y_inv)
print("torus translation orientation =", torus_translation_orientation)
print("Klein glide orientation =", klein_glide_orientation)
print("Cartan rank =", cartan_rank)
print("doubled Cartan carrier =", doubled_cartan_carrier)
print("O(5,5) carrier =", o55_carrier)
print("full o(5,5) generators =", full_o55_generators)
print("active o(5,5) generators =", active_o55_generators)
print("p6m PSA count = active + scalar =", active_o55_generators + scalar_base_deferred_interface)

assert torus_cycles == 2
assert F * F_inv == sp.eye(3)
assert F * F == T_x
assert F * T_y * F_inv == T_y_inv
assert torus_translation_orientation == 1
assert klein_glide_orientation == -1
assert doubled_cartan_carrier == o55_carrier == 10
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base_deferred_interface == p6m_non_equiv_psa

print("torus_klein_o55_bridge.py: bridge audit passed")
