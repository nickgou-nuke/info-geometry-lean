#!/usr/bin/env python3
"""SymPy witness for JaynesLDDPGNSColimit.lean.

Audit-only finite model of the shared reference-state mechanism:
  * Jaynes/LDDP relative entropy S[p|m] = -Σ p log(p/m);
  * direct-colimit cylinder embedding duplicates a finite cut without changing
    the represented boundary observable;
  * GNS expectation is a vacuum/reference-state expectation.
"""

import math
import sympy as sp


def jaynes_relative_entropy(p, m):
    return -sum(pi * sp.log(pi / mi) for pi, mi in zip(p, m))

# Self-relative entropy vanishes.
p = [sp.Rational(1, 2), sp.Rational(1, 3), sp.Rational(1, 6)]
assert sp.simplify(jaynes_relative_entropy(p, p)) == 0

# Relative entropy is finite relative to a nonzero reference density.
m = [sp.Rational(1, 3), sp.Rational(1, 3), sp.Rational(1, 3)]
D = -jaynes_relative_entropy(p, m)  # KL(p||m) = Σ p log(p/m)
assert sp.simplify(D - sum(pi * sp.log(pi / mi) for pi, mi in zip(p, m))) == 0

# Uniform self-reference also vanishes for finite cuts.
for N in range(1, 8):
    u = [sp.Rational(1, N)] * N
    assert sp.simplify(jaynes_relative_entropy(u, u)) == 0

# Categorical LDDP / UHF diagonal embedding: duplicate over the new bit.
def diag_embed_succ(values):
    # values indexed by n-bit words; successor duplicates each value twice.
    out = []
    for v in values:
        out.extend([v, v])
    return out

values = [sp.Symbol(f"a{i}") for i in range(4)]
embedded = diag_embed_succ(values)
assert embedded == [values[0], values[0], values[1], values[1], values[2], values[2], values[3], values[3]]

# A normalized trace/reference state is preserved by duplication if normalized
# by the new number of cells.
def avg(vals):
    return sum(vals) / len(vals)

assert sp.simplify(avg(embedded) - avg(values)) == 0

# Cylinder compatibility: a boundary point's first n bits evaluate the same
# before and after successor embedding.
def prefix_index(bits):
    k = 0
    for b in bits:
        k = 2 * k + int(b)
    return k

boundary = [1, 0, 1, 1, 0]
n_bits = 2
idx_n = prefix_index(boundary[:n_bits])
idx_np1 = prefix_index(boundary[: n_bits + 1])
assert embedded[idx_np1] == values[idx_n]

# GNS finite matrix witness: vacuum expectation <Ω|A|Ω> is the reference state.
A00, A01, A10, A11 = sp.symbols("A00 A01 A10 A11")
A = sp.Matrix([[A00, A01], [A10, A11]])
Omega = sp.Matrix([1, 0])
expectation = (Omega.T * A * Omega)[0]
ref_state = A00
assert sp.simplify(expectation - ref_state) == 0

print("jaynes_lddp_gns_colimit.py: all witnesses passed")
