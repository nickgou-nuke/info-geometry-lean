"""Exact rational readout for the global particle-hole sheet reflection."""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


NMODES = 5
DIM = 2 ** NMODES
I2 = sp.eye(2)
X = sp.Matrix([[0, 1], [1, 0]])
Z = sp.diag(1, -1)
CREATE_1 = sp.Matrix([[0, 0], [1, 0]])
ANNIHILATE_1 = CREATE_1.T
ZERO = sp.zeros(DIM)
IDENTITY = sp.eye(DIM)


def kron_all(factors: list[sp.Matrix]) -> sp.Matrix:
    result = factors[0]
    for factor in factors[1:]:
        result = sp.kronecker_product(result, factor)
    return result


def jw(local: sp.Matrix, mode: int) -> sp.Matrix:
    return kron_all([Z if i < mode else local if i == mode else I2
                     for i in range(NMODES)])


def rank_of(matrices: list[sp.Matrix]) -> int:
    if not matrices:
        return 0
    return sp.Matrix.hstack(*[m.reshape(DIM * DIM, 1)
                              for m in matrices]).rank()


def in_span(candidate: sp.Matrix, basis: list[sp.Matrix]) -> bool:
    return rank_of(basis + [candidate]) == rank_of(basis)


creators = [jw(CREATE_1, i) for i in range(NMODES)]
annihilators = [jw(ANNIHILATE_1, i) for i in range(NMODES)]
number_parts = [creators[i] * annihilators[i] for i in range(NMODES)]
clock = sum(number_parts, ZERO) - sp.Rational(NMODES, 2) * IDENTITY
mirror = kron_all([X] * NMODES)

assert mirror * mirror == IDENTITY
assert mirror * clock * mirror == -clock

cartan = [number_parts[i] - sp.Rational(1, 2) * IDENTITY
          for i in range(NMODES)]
cartan_mirror = [mirror * h * mirror for h in cartan]
assert all(cartan_mirror[i] == -cartan[i] for i in range(NMODES))

positive_one = creators
negative_one = annihilators
positive_two = [creators[i] * creators[j]
                for i in range(NMODES) for j in range(i + 1, NMODES)]
negative_two = [annihilators[i] * annihilators[j]
                for i in range(NMODES) for j in range(i + 1, NMODES)]

assert all(mirror * creators[i] * mirror == (-1) ** i * annihilators[i]
           for i in range(NMODES))
assert all(mirror * annihilators[i] * mirror == (-1) ** i * creators[i]
           for i in range(NMODES))
assert all(in_span(mirror * x * mirror, negative_one)
           for x in positive_one)
assert all(in_span(mirror * x * mirror, positive_one)
           for x in negative_one)
assert all(in_span(mirror * x * mirror, negative_two)
           for x in positive_two)
assert all(in_span(mirror * x * mirror, positive_two)
           for x in negative_two)

report = {
    "coefficient_field": "QQ",
    "carrier_dimension": DIM,
    "mirror_square": True,
    "cartan_action": "H_i -> -H_i",
    "clock_action": "N -> -N",
    "grade_exchange": {
        "+1": "-1",
        "+2": "-2",
        "-1": "+1",
        "-2": "+2",
        "0": "0",
    },
    "creation_annihilation_exchange": True,
    "scope": "global_sheet_reflection_readout",
}

output = Path("tools/experiments/cl55_five_grade/export/cartan_sheet_readout.json")
output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print("SYMPY:global_sheet_reflection=true")
print("SYMPY:clock_reversal=true")
print("SYMPY:grade_exchange=+/-1,+/-2")
print("SYMPY:report=%s" % output)
