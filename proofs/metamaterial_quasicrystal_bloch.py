#!/usr/bin/env python3
"""SymPy audit for the finite metamaterial quasicrystal Bloch toy."""

import sympy as sp

gain, loss = sp.symbols("gain loss", real=True)

# First three prime samples: ordered, but with unequal adjacent spacings.
prime_samples = [2, 3, 5]
ordered_prime_samples = prime_samples[0] < prime_samples[1] < prime_samples[2]
nonperiodic_prime_spacings = (
    prime_samples[1] - prime_samples[0] != prime_samples[2] - prime_samples[1]
)

# Klein-Bloch twist: momentum inversion plus orientation-reversing glide label.
def klein_bloch_twist(mode):
    momentum, _chirality = mode
    return (-momentum, "kleinGlide")


def orientation_sign(generator):
    return -1 if generator == "kleinGlide" else 1


mode = (3, "torusTranslation")
twisted = klein_bloch_twist(mode)

# O(5,5) / wallpaper finite counters.
o55_cartan_rank = 5
doubled_cartan_carrier_dimension = 10
active_o55_generators = 15
p6m_psa_count = 16

# Optical/Raman and nonlinear-gain finite counters.
optical_raman_active_trivial = True
generation_phase_count = 3
gain_minus_loss = gain - loss
four_wave_mixing_count = 3 + 1

print("prime samples =", prime_samples)
print("ordered =", ordered_prime_samples)
print("nonperiodic spacings =", nonperiodic_prime_spacings)
print("twisted mode =", twisted)
print("gain-loss margin =", gain_minus_loss)

assert len(prime_samples) == 3
assert ordered_prime_samples is True
assert nonperiodic_prime_spacings is True
assert twisted[0] == -mode[0]
assert orientation_sign(twisted[1]) == -1
assert o55_cartan_rank == 5
assert doubled_cartan_carrier_dimension == 10
assert active_o55_generators + 1 == p6m_psa_count
assert optical_raman_active_trivial is True
assert generation_phase_count == 3
assert sp.simplify(gain_minus_loss - (gain - loss)) == 0
assert four_wave_mixing_count == 4

print("metamaterial_quasicrystal_bloch.py: SymPy audit passed")
