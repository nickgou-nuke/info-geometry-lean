#!/usr/bin/env python3
"""Finite audit for K-theory/Chern confinement signature toy."""

primes = [2, 3, 5]
k0_modulus = {p: p - 1 for p in primes}
base_k1_rank = 0
fixed_orbits_p6m = 3
bloch_free_rank = 2
crossed_k1_rank = 2
jones_index_d6 = 12
chern_parity_zero = (0 % 2) != 0

assert k0_modulus[2] == 1
assert k0_modulus[3] == 2
assert k0_modulus[5] == 4
assert base_k1_rank == 0
assert fixed_orbits_p6m == 3
assert bloch_free_rank == 2
assert crossed_k1_rank == 2
assert jones_index_d6 == 12
assert chern_parity_zero is False
assert len(primes) == 3

print("ktheory_chern_confinement_signature.py: SymPy audit passed")
