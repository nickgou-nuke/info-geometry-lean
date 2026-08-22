#!/usr/bin/env python3
"""Symbolically derive the so(7) stabilizer of the standard G2 3-form."""

import sympy as sp
from itertools import combinations

triples = (
    ((0, 1, 2), 1), ((0, 3, 4), 1), ((0, 5, 6), 1),
    ((1, 3, 5), 1), ((1, 4, 6), -1), ((2, 3, 6), -1),
    ((2, 4, 5), -1),
)

def skew(i, j):
    matrix = sp.zeros(7)
    matrix[i, j] = 1
    matrix[j, i] = -1
    return matrix

def phi(i, j, k):
    if len({i, j, k}) < 3:
        return sp.Integer(0)
    target = tuple(sorted((i, j, k)))
    signed = dict(triples)
    if target not in signed:
        return sp.Integer(0)
    inversions = sum(a > b for n, a in enumerate((i, j, k)) for b in (i, j, k)[n + 1:])
    return signed[target] * sp.Integer(-1 if inversions % 2 else 1)

pairs = list(combinations(range(7), 2))
vars = sp.symbols(f'x0:{len(pairs)}')
A = sp.zeros(7)
for x, (i, j) in zip(vars, pairs):
    A[i, j] = x
    A[j, i] = -x

equations = []
for i, j, k in combinations(range(7), 3):
    equations.append(sp.expand(sum(
        A[i, p] * phi(p, j, k) +
        A[j, p] * phi(i, p, k) +
        A[k, p] * phi(i, j, p)
        for p in range(7))))

coefficient_matrix = sp.linear_eq_to_matrix(equations, vars)[0]
basis = coefficient_matrix.nullspace()
assert len(basis) == 14, len(basis)

def vector_matrix(vector):
    matrix = sp.zeros(7)
    for value, (i, j) in zip(vector, pairs):
        matrix[i, j] = value
        matrix[j, i] = -value
    return matrix

matrices = [vector_matrix(vector) for vector in basis]
columns = sp.Matrix.hstack(*(sp.Matrix([matrix[i, j]
    for i in range(7) for j in range(7)]) for matrix in matrices))
assert columns.rank() == 14

for left in matrices:
    for right in matrices:
        bracket = left * right - right * left
        assert sp.linsolve((columns, sp.Matrix([bracket[i, j]
            for i in range(7) for j in range(7)]))) != sp.EmptySet

def legacy(i, j, sign=1):
    return sp.Rational(1, 2) * (sign * skew(i, j))

legacy_generators = [
    legacy(1, 2) - legacy(3, 4),
    -legacy(0, 2) - legacy(3, 5),
    legacy(0, 1) + legacy(3, 6),
    -legacy(0, 4) + legacy(1, 5),
    legacy(0, 3) - legacy(1, 6),
    legacy(0, 6) + legacy(1, 3),
    -legacy(0, 5) - legacy(1, 4),
    legacy(3, 4) - legacy(5, 6),
    legacy(3, 5) + legacy(4, 6),
    -legacy(3, 6) + legacy(4, 5),
    -legacy(1, 5) - legacy(2, 6),
    -legacy(1, 6) + legacy(2, 5),
    -legacy(0, 6) + legacy(2, 4),
    legacy(1, 4) - legacy(2, 3),
]
legacy_columns = sp.Matrix.hstack(*(sp.Matrix([matrix[i, j]
    for i in range(7) for j in range(7)]) for matrix in legacy_generators))
assert legacy_columns.rank() == 14
assert legacy_columns.row_join(columns).rank() == 14
for left in legacy_generators:
    for right in legacy_generators:
        bracket = left * right - right * left
        assert sp.linsolve((legacy_columns, sp.Matrix([bracket[i, j]
            for i in range(7) for j in range(7)]))) != sp.EmptySet

ad = legacy_generators[0] * legacy_generators[3] - legacy_generators[3] * legacy_generators[0]
ad_coordinates = next(iter(sp.linsolve((legacy_columns, sp.Matrix([
    ad[i, j] for i in range(7) for j in range(7)])))))
assert ad_coordinates[4] == sp.Rational(1, 2)
assert ad_coordinates[11] == -sp.Rational(1, 2)
assert all(ad_coordinates[i] == 0 for i in range(14) if i not in (4, 11))

ab = legacy_generators[0] * legacy_generators[1] - legacy_generators[1] * legacy_generators[0]
ab_claim = -sp.Rational(1, 2) * (legacy_generators[2] + legacy_generators[9])
assert ab == ab_claim
ab_coordinates = next(iter(sp.linsolve((legacy_columns, sp.Matrix([
    ab[i, j] for i in range(7) for j in range(7)])))))
print(f"BRACKET_A_B_COORDINATES={ab_coordinates}")

ac = legacy_generators[0] * legacy_generators[2] - legacy_generators[2] * legacy_generators[0]
ac_claim = sp.Rational(1, 2) * (legacy_generators[1] + legacy_generators[8])
assert ac == ac_claim

ae = legacy_generators[0] * legacy_generators[4] - legacy_generators[4] * legacy_generators[0]
ae_claim = -sp.Rational(1, 2) * (legacy_generators[3] + legacy_generators[10])
assert ae == ae_claim

af = legacy_generators[0] * legacy_generators[5] - legacy_generators[5] * legacy_generators[0]
af_claim = sp.Rational(1, 2) * legacy_generators[13]
assert af == af_claim

print("G2_SO7_STABILIZER_DIM=14")
for n, vector in enumerate(basis):
    support = [(pairs[i], value) for i, value in enumerate(vector) if value]
    print(f"GENERATOR_{n}={support}")
print("SYMBOLIC_LINEAR_STABILIZER=PASS")
print("SYMBOLIC_BRACKET_CLOSURE=PASS")
print("CORRECTED_LEGACY_D_SIGN=PASS")
print("CORRECTED_LEGACY_BRACKET_CLOSURE=PASS")
print("BRACKET_A_D=1/2*(E-L)")
print("BRACKET_A_B=-1/2*(C+J)")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
