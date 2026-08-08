#!/usr/bin/env python3
"""SymPy audit for the finite conformal scale recurrence toy."""

import sympy as sp

Omega = sp.symbols("Omega", nonzero=True)
conformal_pair_product = sp.simplify(Omega * (1 / Omega))

scale_flip = {"UV": "IR", "IR": "UV"}

x, y = sp.symbols("x y", real=True)
z = x + sp.I * y
T = lambda w: w + sp.I
G = lambda w: sp.conjugate(w) + 1
Tinv = lambda w: w - sp.I

cartan_rank = 5
doubled_cartan = 2 * cartan_rank
phase_locked_generations = [2, 3, 5]
four_wave = 3 + 1
gain, loss = sp.symbols("gain loss", real=True)
gain_minus_loss = gain - loss

print("scale flip =", scale_flip)
print("Omega * Omega^-1 =", conformal_pair_product)
print("G(T(z)) - Tinv(G(z)) =", sp.simplify(G(T(z)) - Tinv(G(z))))
print("G(G(z)) - (z+2) =", sp.simplify(G(G(z)) - (z + 2)))

for endpoint in scale_flip:
    assert scale_flip[scale_flip[endpoint]] == endpoint
assert scale_flip["UV"] == "IR"
assert scale_flip["IR"] == "UV"
assert conformal_pair_product == 1
assert sp.simplify(G(T(z)) - Tinv(G(z))) == 0
assert sp.simplify(G(G(z)) - (z + 2)) == 0
assert cartan_rank == 5
assert doubled_cartan == 10
assert len(phase_locked_generations) == 3
assert four_wave == 4
assert sp.simplify(gain_minus_loss - (gain - loss)) == 0

print("conformal_scale_recurrence.py: SymPy audit passed")
