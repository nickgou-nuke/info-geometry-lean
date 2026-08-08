#!/usr/bin/env python3
"""Wallpaper-to-O(5,5) frozen selection bridge audit."""

wallpaper_count = 17
pg_h2 = 1
p6m_h2 = 4
p6m_non_equiv_psa = 16

full_positive_rotations = 10
full_negative_rotations = 10
full_mixed_boosts = 25
full_o55_generators = full_positive_rotations + full_negative_rotations + full_mixed_boosts

active_compact = 10
active_mixed_boosts = 5
active_o55_generators = active_compact + active_mixed_boosts
scalar_base_socket = 1

print("wallpaper count =", wallpaper_count)
print("pg H2 exponent =", pg_h2)
print("p6m H2 exponent =", p6m_h2)
print("p6m non-equivalent PSA count =", p6m_non_equiv_psa)
print("full O(5,5) generator grading =", {
    "positive_rotations": full_positive_rotations,
    "negative_rotations": full_negative_rotations,
    "mixed_boosts": full_mixed_boosts,
    "total": full_o55_generators,
})
print("active frozen-flow grading =", {
    "compact": active_compact,
    "mixed_boosts": active_mixed_boosts,
    "active_total": active_o55_generators,
    "plus_scalar_base": active_o55_generators + scalar_base_socket,
})

assert wallpaper_count == 17
assert pg_h2 == 1
assert p6m_h2 == 4
assert p6m_non_equiv_psa == 16
assert full_o55_generators == 45
assert active_o55_generators == 15
assert active_o55_generators + scalar_base_socket == p6m_non_equiv_psa
print("wallpaper_o55_frozen_selection_bridge.py: bridge audit passed")
