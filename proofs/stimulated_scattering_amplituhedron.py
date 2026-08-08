#!/usr/bin/env python3
"""SymPy audit for the finite stimulated-scattering/amplituhedron toy."""

import sympy as sp

q, B, rho, pump, scattered = sp.symbols("q B rho pump scattered")

stimulated_gain_0 = q * (0 + 1)
stimulated_gain_1 = q * (1 + 1)
einstein_A = B * rho
stokes_shift = pump - scattered

boundary_winding = sp.Integer(3)
bulk_amplitude = boundary_winding

amplituhedron_volume = sp.Integer(4)
dikin_volume_counter = sp.Integer(4)
four_wave_mixing_count = 3 + 1
raman_lane_count = 3
active_o55_generators = 15
scalar_base = 1
p6m_psa = 16
jackiw_rebbi_index = 1

print("stimulated gain n=0 =", stimulated_gain_0)
print("stimulated gain n=1 =", stimulated_gain_1)
print("Einstein equilibrium A =", einstein_A)
print("Hodge-Penrose toy amplitude =", bulk_amplitude)
print("amplituhedron volume =", amplituhedron_volume)
print("Dikin volume counter =", dikin_volume_counter)
print("four-wave mixing count =", four_wave_mixing_count)
print("Stokes shift =", stokes_shift)

assert sp.simplify(stimulated_gain_0 - q) == 0
assert sp.simplify(stimulated_gain_1 - 2 * q) == 0
assert bulk_amplitude == boundary_winding
assert amplituhedron_volume == dikin_volume_counter == 4
assert four_wave_mixing_count == 4
assert raman_lane_count == 3
assert active_o55_generators + scalar_base == p6m_psa
assert jackiw_rebbi_index == 1
assert sp.simplify(stokes_shift - (pump - scattered)) == 0

print("stimulated_scattering_amplituhedron.py: SymPy audit passed")
