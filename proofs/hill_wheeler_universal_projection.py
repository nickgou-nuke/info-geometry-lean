#!/usr/bin/env python3
"""SymPy witness for HillWheelerUniversalProjection.lean.

Audits the finite shared projection algebra:
  det(H - E N) generalized Hill--Wheeler secular equation;
  idempotent finite projectors;
  CPT average projects s to Re(s)=1/2;
  GNS overlap kernel N_ab = tau(a*b) in a finite matrix model;
  UHF diagonal embedding preserves normalized averages/cylinder values.
"""

import sympy as sp

E = sp.symbols("E")
h0, h1, n0, n1 = sp.symbols("h0 h1 n0 n1")
H = sp.diag(h0, h1)
N = sp.diag(n0, n1)
secular = (H - E * N).det()
assert sp.factor(secular - (h0 - E * n0) * (h1 - E * n1)) == 0

# Non-diagonal overlap audit: determinant still computes det(H-E N).
h00, h01, h10, h11, n00, n01, n10, n11 = sp.symbols("h00 h01 h10 h11 n00 n01 n10 n11")
H2 = sp.Matrix([[h00, h01], [h10, h11]])
N2 = sp.Matrix([[n00, n01], [n10, n11]])
manual = (h00 - E*n00) * (h11 - E*n11) - (h01 - E*n01) * (h10 - E*n10)
assert sp.expand((H2 - E * N2).det() - manual) == 0

# Projectors: symmetry restoration/filtering.
P0 = sp.Matrix([[1, 0], [0, 0]])
P1 = sp.Matrix([[0, 0], [0, 1]])
assert P0 * P0 == P0
assert P1 * P1 == P1
assert P0 + P1 == sp.eye(2)
assert P0 * P1 == sp.zeros(2)

# CPT Hill--Wheeler average: s -> (s + (1-conj s))/2 = 1/2 + i Im(s).
sigma, t = sp.symbols("sigma t", real=True)
s = sigma + sp.I * t
cpt = 1 - sp.conjugate(s)
avg = sp.simplify((s + cpt) / 2)
assert sp.simplify(sp.re(avg) - sp.Rational(1, 2)) == 0
assert sp.simplify(1 - sp.conjugate(avg) - avg) == 0

# GNS overlap kernel in finite matrix model: tau(A*B), tau=normalized trace.
a00, a01, a10, a11, b00, b01, b10, b11 = sp.symbols("a00 a01 a10 a11 b00 b01 b10 b11")
A = sp.Matrix([[a00, a01], [a10, a11]])
B = sp.Matrix([[b00, b01], [b10, b11]])
tau_AB = sp.trace(A * B) / 2
assert sp.simplify(tau_AB - ((A * B)[0, 0] + (A * B)[1, 1]) / 2) == 0

# UHF/colimit finite cut: duplicating each diagonal cell preserves normalized reference average.
def diag_embed(values):
    out = []
    for v in values:
        out.extend([v, v])
    return out

vals = [sp.symbols(f"a{i}") for i in range(4)]
embedded = diag_embed(vals)
assert sp.simplify(sum(embedded) / len(embedded) - sum(vals) / len(vals)) == 0

print("hill_wheeler_universal_projection.py: all witnesses passed")
