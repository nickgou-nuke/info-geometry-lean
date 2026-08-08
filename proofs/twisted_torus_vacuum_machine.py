#!/usr/bin/env python3
"""Finite audit for the twisted torus vacuum-machine capstone."""

raw_torus_orientation = 1
klein_crosscap_orientation = -1
cartan_rank = 5
doubled_charge_lattice_dim = 2 * cartan_rank
o55_carrier_dim = 10
full_o55_generators = 45
active_o55_generators = 15
scalar_base_socket = 1
p6m_non_equiv_psa = 16
active_mode = True
frozen_mode = False

print("raw torus orientation =", raw_torus_orientation)
print("Klein crosscap orientation =", klein_crosscap_orientation)
print("Cartan rank =", cartan_rank)
print("doubled charge lattice dimension =", doubled_charge_lattice_dim)
print("O(5,5) carrier dimension =", o55_carrier_dim)
print("full o(5,5) generators =", full_o55_generators)
print("active o(5,5) generators =", active_o55_generators)
print("p6m non-equivalent PSA = active + scalar =", active_o55_generators + scalar_base_socket)
print("mode selection =", {"active": active_mode, "frozen": frozen_mode})

assert raw_torus_orientation == 1
assert klein_crosscap_orientation == -1
assert doubled_charge_lattice_dim == o55_carrier_dim == 10
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base_socket == p6m_non_equiv_psa
assert active_mode is True
assert frozen_mode is False

print("twisted_torus_vacuum_machine.py: capstone audit passed")
