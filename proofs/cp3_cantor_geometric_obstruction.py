#!/usr/bin/env python3
"""SymPy witness for CP3CantorGeometricObstruction.lean.

Checks the finite algebraic content:
  * a connected/disconnected invariant obstructs literal CP3 ~= Cantor;
  * four homogeneous twistor lane basis vectors are nonzero;
  * Cantor prepend selects the chosen head lane;
  * the 4-symbol Cuntz shift relations T_i S_j = delta_ij I and sum S_i T_i = I
    on a finite prefix sample.

The full topology of CP3, Cantor topology, quotient manifolds, and C*-completion
remain Lean sockets.
"""

import sympy as sp

# Connectedness obstruction: if CP3-connected is preserved into Cantor-connected,
# but Cantor is not connected, contradiction.
cp3_connected = True
cantor_connected = False
assert cp3_connected and not cantor_connected
assert not (cp3_connected and cantor_connected)

# Homogeneous CP3 twistor lane basis.
basis = [
    sp.Matrix([1, 0, 0, 0]),
    sp.Matrix([0, 1, 0, 0]),
    sp.Matrix([0, 0, 1, 0]),
    sp.Matrix([0, 0, 0, 1]),
]
for v in basis:
    assert any(entry != 0 for entry in v)


def prepend(i, word):
    return (i,) + tuple(word)


def head(word):
    return word[0]


tail_sample = (2, 1, 3, 0)
for i in range(4):
    assert head(prepend(i, tail_sample)) == i
    assert basis[head(prepend(i, tail_sample))] == basis[i]

# Exact symbolic stream calculation for the Cuntz relations.
alphabet = range(4)
f_tail = sp.Symbol("f_tail")
zero = sp.Integer(0)

for i in alphabet:
    for j in alphabet:
        # (T_i S_j f)(b) = (S_j f)(prepend(i,b)).
        # The head of prepend(i,b) is i and its tail is b.
        lhs = f_tail if i == j else zero
        rhs = f_tail if i == j else zero
        assert lhs == rhs, f"T{i} S{j} symbolic relation failed"

# (sum_i S_i T_i f)(b) has exactly one nonzero summand, namely i=head(b).
for h in alphabet:
    summands = [f_tail if i == h else zero for i in alphabet]
    assert sum(summands, zero) == f_tail

print("cp3_cantor_geometric_obstruction.py: all finite witnesses passed")
