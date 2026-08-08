#!/usr/bin/env python3
"""SymPy witness for CuntzBoundarySolderRealization.lean.

Audit-only finite checks for the representation story:
  * a finite-depth 4-ary Cantor cylinder has creation/annihilation shifts with
    exact interior Cuntz relations T_i S_j = δ_ij I on the depth-(d-1) domain;
  * partition Σ S_i T_i = I on the depth-d cylinder;
  * Gell-Mann soldering acts on three color lanes and leaves singlet neutral;
  * a seed SU(3) commutator transports through a Weyl permutation.
"""

import itertools
import sympy as sp

I = sp.I


def words(depth, alphabet=4):
    return list(itertools.product(range(alphabet), repeat=depth))


def creation_matrix(symbol: int, depth: int):
    """S_i: functions on depth-1 cylinders -> functions on depth cylinders.
    (S_i f)(w) = f(tail(w)) if head(w)=i, else 0.
    Matrix shape: 4^depth × 4^(depth-1).
    """
    cod = words(depth)
    dom = words(depth - 1)
    dom_index = {w: k for k, w in enumerate(dom)}
    M = sp.zeros(len(cod), len(dom))
    for r, w in enumerate(cod):
        if w[0] == symbol:
            M[r, dom_index[w[1:]]] = 1
    return M


def annihilation_matrix(symbol: int, depth: int):
    """T_i: functions on depth cylinders -> functions on depth-1 cylinders.
    (T_i f)(u) = f(i,u).
    Matrix shape: 4^(depth-1) × 4^depth.
    """
    dom = words(depth)
    cod = words(depth - 1)
    dom_index = {w: k for k, w in enumerate(dom)}
    M = sp.zeros(len(cod), len(dom))
    for r, u in enumerate(cod):
        M[r, dom_index[(symbol,) + u]] = 1
    return M


def assert_zero(M, name):
    Z = sp.simplify(M)
    if isinstance(Z, sp.MatrixBase):
        assert Z == sp.zeros(*Z.shape), f"{name} failed:\n{Z}"
    else:
        assert Z == 0, f"{name} failed: {Z}"

# Finite cylinder witnesses for Cuntz relations.
depth = 3
S = [creation_matrix(i, depth) for i in range(4)]
T = [annihilation_matrix(i, depth) for i in range(4)]
I_small = sp.eye(4 ** (depth - 1))
I_big = sp.eye(4 ** depth)

for i in range(4):
    for j in range(4):
        expected = I_small if i == j else sp.zeros(4 ** (depth - 1))
        assert_zero(T[i] * S[j] - expected, f"T{i} S{j}")

partition = sum((S[i] * T[i] for i in range(4)), sp.zeros(4 ** depth))
assert_zero(partition - I_big, "partition unity")

# Gell-Mann / Weyl solder witness.
gl1 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
gl2 = sp.Matrix([[0, -I, 0], [I, 0, 0], [0, 0, 0]])
gl3 = sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
P12 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
P23 = sp.Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])

p0, p1, p2, ell = sp.symbols("p0 p1 p2 ell")
color = sp.Matrix([p0, p1, p2])


def act(A, c=color):
    return A * c, 0

# Singlet neutrality.
for A in [gl1, gl2, gl3, P12 * gl1 * P12, P23 * gl1 * P23]:
    assert act(A)[1] == 0

# Seed commutator and Weyl transport.
assert_zero(gl1 * gl2 - gl2 * gl1 - 2 * I * gl3, "seed [gl1,gl2]")
for P, name in [(P12, "P12"), (P23, "P23")]:
    A = P * gl1 * P
    B = P * gl2 * P
    C = P * gl3 * P
    assert_zero(A * B - B * A - 2 * I * C, f"{name} transported matrix")
    lhs, sing = act(A, act(B)[0])
    rhs = act(B, act(A)[0])[0]
    target = act(2 * I * C)[0]
    assert_zero(lhs - rhs - target, f"{name} transported action")
    assert sing == 0

print("cuntz_boundary_solder_realization.py: all witnesses passed")
