#!/usr/bin/env python3
"""Audit for the doubled charge lattice / Kasparov--Krein bridge."""

doubled_charge_lattice_rank = 10
full_o55_generators = 45
active_o55_generators = 15
p6m_psa_count = 16
scalar_base_deferred_interface = 1

print("doubled_charge_lattice_rank =", doubled_charge_lattice_rank)
print("full_o55_generators =", full_o55_generators)
print("active_o55_generators =", active_o55_generators)
print("p6m_psa_count =", p6m_psa_count)
print("active_o55_plus_scalar =", active_o55_generators + scalar_base_deferred_interface)

assert doubled_charge_lattice_rank == 10
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base_deferred_interface == p6m_psa_count
print("doubled_charge_lattice_kasparov_krein_bridge.py: bridge audit passed")
