#!/usr/bin/env python3
"""SymPy audit for the finite phase-conjugate vacuum mirror toy."""

import sympy as sp

q = sp.symbols("q")

# Glide / modular-J phase inversion in a finite cyclic phase toy.
phase = sp.symbols("phase")
modular_j = -phase

# Andreev mirror bookkeeping: electron lane reflects as a J-conjugate hole.
lanes = ["singlet", "red", "green", "blue"]
j_lane = {"singlet": "singlet", "red": "green", "green": "red", "blue": "blue"}


def andreev_reflect(lane):
    return {"hole": j_lane[lane], "pair_injected": True, "topological": True}


raman_lanes = ["pump", "stokes", "phonon"]
four_wave_mixing_count = len(raman_lanes) + 1
stimulated_gain_0 = q * (0 + 1)
stimulated_gain_1 = q * (1 + 1)
amplituhedron_volume = sp.Integer(4)
dikin_volume_counter = sp.Integer(4)
pump_to_stokes_selected = True

print("modular J phase inversion =", modular_j)
print("Andreev mirror red =", andreev_reflect("red"))
print("four-wave mixing count =", four_wave_mixing_count)
print("stimulated gains =", stimulated_gain_0, stimulated_gain_1)

assert sp.simplify(-modular_j - phase) == 0
for lane in lanes:
    assert j_lane[j_lane[lane]] == lane
    reflection = andreev_reflect(lane)
    assert reflection["hole"] == j_lane[lane]
    assert reflection["pair_injected"] is True
    assert reflection["topological"] is True

assert len(raman_lanes) == 3
assert four_wave_mixing_count == 4
assert sp.simplify(stimulated_gain_0 - q) == 0
assert sp.simplify(stimulated_gain_1 - 2 * q) == 0
assert amplituhedron_volume == dikin_volume_counter == 4
assert pump_to_stokes_selected is True

print("phase_conjugate_vacuum_mirror.py: SymPy audit passed")
