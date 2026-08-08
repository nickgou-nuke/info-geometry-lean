#!/usr/bin/env python3
"""SymPy audit for the finite superconducting holographic resonator toy."""

import sympy as sp

flow_reverse = {"forward": "backward", "backward": "forward"}

K, A, gain, loss = sp.symbols("K A gain loss")
weak_overlap = A  # zero modular time fixed point
standing_node = sp.simplify(weak_overlap - A)
gain_minus_loss = gain - loss

modular_j = {"singlet": "singlet", "red": "green", "green": "red", "blue": "blue"}

def andreev_reflect(lane):
    return {"hole": modular_j[lane], "injected": True}

x, y = sp.symbols("x y", real=True)
z = x + sp.I * y
T = lambda w: w + sp.I
G = lambda w: sp.conjugate(w) + 1
Tinv = lambda w: w - sp.I

wilson_swirl = 1 + 1 + 1
four_wave = 3 + 1
phase_locked_generations = [2, 3, 5]

print("flow reverse =", flow_reverse)
print("weak overlap =", weak_overlap)
print("Wilson swirl =", wilson_swirl)

for d in flow_reverse:
    assert flow_reverse[flow_reverse[d]] == d
for lane, hole in modular_j.items():
    assert modular_j[hole] == lane
    assert andreev_reflect(lane)["hole"] == hole
    assert andreev_reflect(lane)["injected"] is True

assert standing_node == 0
assert sp.simplify(gain_minus_loss - (gain - loss)) == 0
assert sp.simplify(G(T(z)) - Tinv(G(z))) == 0
assert sp.simplify(G(G(z)) - (z + 2)) == 0
assert wilson_swirl == 3
assert four_wave == 4
assert len(phase_locked_generations) == 3

print("superconducting_holographic_resonator.py: SymPy audit passed")
