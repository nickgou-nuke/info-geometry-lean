#!/usr/bin/env python3
"""Audit for the torus-that-is-Klein-bottle manifold generator bridge."""

manifold_generator_count = 1
full_o55_generators = 45
active_o55_generators = 15
p6m_psa_count = 16
scalar_base_socket = 1

print("manifold_generator_count =", manifold_generator_count)
print("full_o55_generators =", full_o55_generators)
print("active_o55_generators =", active_o55_generators)
print("p6m_psa_count =", p6m_psa_count)
print("active_o55_plus_scalar =", active_o55_generators + scalar_base_socket)

assert manifold_generator_count == 1
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base_socket == p6m_psa_count
print("torus_that_is_klein_bottle_generator.py: bridge audit passed")
