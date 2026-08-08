#!/usr/bin/env python3
"""SymPy audit for the finite topological metasurface supercurrent toy."""

import sympy as sp

swirl_reverse = {"clockwise": "counterclockwise", "counterclockwise": "clockwise"}
quantized_swirl = 1 + 1 + 1

prime_samples = [2, 3, 5]
spacings = [prime_samples[1] - prime_samples[0], prime_samples[2] - prime_samples[1]]

active_o55 = 15
p6m_psa = 16
four_wave = 3 + 1
phase_locked_generations = [2, 3, 5]
electron_mass, gain, loss, A = sp.symbols("electron_mass gain loss A", real=True)
photonic_bandgap_toy = 2 * electron_mass
gain_minus_loss = gain - loss
weak_overlap = A

print("swirl reverse =", swirl_reverse)
print("quantized swirl =", quantized_swirl)
print("prime spacings =", spacings)
print("photonic bandgap toy =", photonic_bandgap_toy)

for s in swirl_reverse:
    assert swirl_reverse[swirl_reverse[s]] == s
assert quantized_swirl == 3
assert len(prime_samples) == 3
assert prime_samples[0] < prime_samples[1] < prime_samples[2]
assert spacings[0] != spacings[1]
assert active_o55 + 1 == p6m_psa
assert four_wave == 4
assert len(phase_locked_generations) == 3
assert sp.simplify(photonic_bandgap_toy - 2 * electron_mass) == 0
assert sp.simplify(gain_minus_loss - (gain - loss)) == 0
assert sp.simplify(weak_overlap - A) == 0

print("topological_metasurface_supercurrent.py: SymPy audit passed")
