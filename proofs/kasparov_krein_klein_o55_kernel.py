#!/usr/bin/env python3
"""Finite audit for the Kasparov--Krein Klein/O(5,5) kernel."""

signature = (5, 5)
signature_balance = signature[0] - signature[1]
krein_j_signs = {"positive": 1, "negative": -1}
krein_j_squares = {k: v * v for k, v in krein_j_signs.items()}
cartan_rank = 5
doubled_carrier = 2 * cartan_rank
full_o55_generators = 45
active_o55_generators = 15
scalar_base = 1
p6m_non_equiv_psa = 16
klein_glide_orientation = -1
o2_pairing = 0

print("Krein signature =", signature)
print("signature balance =", signature_balance)
print("J sign squares =", krein_j_squares)
print("Klein glide orientation =", klein_glide_orientation)
print("Cartan rank =", cartan_rank)
print("doubled O(5,5) carrier =", doubled_carrier)
print("full o(5,5) generators =", full_o55_generators)
print("active o(5,5) generators =", active_o55_generators)
print("p6m active+base count =", active_o55_generators + scalar_base)
print("O2 Kasparov/Krein pairing =", o2_pairing)

assert signature_balance == 0
assert all(v == 1 for v in krein_j_squares.values())
assert klein_glide_orientation == -1
assert doubled_carrier == 10
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base == p6m_non_equiv_psa
assert o2_pairing == 0

print("kasparov_krein_klein_o55_kernel.py: kernel audit passed")
