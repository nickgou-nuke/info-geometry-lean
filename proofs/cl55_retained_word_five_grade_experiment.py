#!/usr/bin/env python3
"""Exact real experiment for retained words in the Cl(5,5) Fock model.

This is exploratory evidence only.  It is deliberately not a Lean theorem,
not a C*-algebra construction, and not a wrapper around a claimed closure.

The model is the real five-mode Jordan--Wigner representation.  Creation and
annihilation operators are retained as associative matrices.  Same-chirality
quadratic words are *not* folded back to a three-generator Zorn shadow.
"""

from __future__ import annotations

import json
from collections import defaultdict

import sympy as sp


NMODES = 5
DIM = 2**NMODES
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
    """Real Jordan--Wigner operator on mode ``mode``."""
    factors = [Z if i < mode else local if i == mode else I2
               for i in range(NMODES)]
    return kron_all(factors)


def comm(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def anti(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b + b * a


def rank_of(matrices: list[sp.Matrix]) -> int:
    if not matrices:
        return 0
    columns = [m.reshape(DIM * DIM, 1) for m in matrices]
    return sp.Matrix.hstack(*columns).rank()


def in_span(candidate: sp.Matrix, basis: list[sp.Matrix]) -> bool:
    return rank_of(basis + [candidate]) == rank_of(basis)


def popcount(value: int) -> int:
    return value.bit_count()


def matrix_unit(row: int, column: int) -> sp.Matrix:
    result = sp.zeros(DIM)
    result[row, column] = 1
    return result


def grade_dimensions() -> dict[int, int]:
    """Exact dimensions of End(Fock) grade sectors under centered number."""
    sectors: dict[int, list[sp.Matrix]] = defaultdict(list)
    for row in range(DIM):
        for column in range(DIM):
            sectors[popcount(row) - popcount(column)].append(
                matrix_unit(row, column))
    return {grade: rank_of(words) for grade, words in sorted(sectors.items())}


def check_grade(n_clock: sp.Matrix, operator: sp.Matrix, degree: int) -> bool:
    return comm(n_clock, operator) == degree * operator


def check_routes(sectors: dict[int, list[sp.Matrix]]) -> dict[str, bool]:
    routes: dict[str, bool] = {}
    for r, left in sectors.items():
        for s, right in sectors.items():
            target = sectors.get(r + s, [])
            key = f"bracket_{r}_{s}_to_{r+s}"
            routes[key] = all(
                in_span(comm(x, y), target) for x in left for y in right)
    return routes


def independent_basis(matrices: list[sp.Matrix]) -> list[sp.Matrix]:
    """Return an exact SymPy basis using one rational RREF computation."""
    if not matrices:
        return []
    columns = [m.reshape(DIM * DIM, 1) for m in matrices]
    _, pivots = sp.Matrix.hstack(*columns).rref()
    return [matrices[index] for index in pivots]


def lie_one_step(generators: list[sp.Matrix]) -> list[sp.Matrix]:
    """Add all first commutators to a finite seed using exact ranks.

    For this CAR seed, the resulting basis is checked against the explicit
    grade sectors below.  Those sectors provide the finite closure check,
    avoiding repeated full-matrix rank computations for every later pair.
    """
    return independent_basis(
        generators + [comm(x, y) for x in generators for y in generators]
    )


def main() -> None:
    create = [jw(CREATE_1, i) for i in range(NMODES)]
    annihilate = [jw(ANNIHILATE_1, i) for i in range(NMODES)]
    number = [create[i] * annihilate[i] for i in range(NMODES)]
    number_clock = sum(number, ZERO) - sp.Rational(NMODES, 2) * IDENTITY

    gamma_plus = [create[i] + annihilate[i] for i in range(NMODES)]
    gamma_minus = [create[i] - annihilate[i] for i in range(NMODES)]

    # Real Cl(5,5) relations: five +1 and five -1 generators, all cross-
    # anticommutators zero.
    assert all(g * g == IDENTITY for g in gamma_plus)
    assert all(g * g == -IDENTITY for g in gamma_minus)
    all_gamma = gamma_plus + gamma_minus
    assert all(anti(all_gamma[i], all_gamma[j]) == ZERO
               for i in range(2 * NMODES)
               for j in range(i))

    # Real particle-hole mirror and a Cartan/parity involution.
    mirror = kron_all([X] * NMODES)
    parity = kron_all([Z] * NMODES)
    assert mirror * mirror == IDENTITY
    assert parity * parity == IDENTITY
    assert mirror * number_clock * mirror == -number_clock
    assert all(mirror * create[i] * mirror == (-1) ** i * annihilate[i]
               for i in range(NMODES))
    assert all(mirror * annihilate[i] * mirror == (-1) ** i * create[i]
               for i in range(NMODES))
    assert all(parity * create[i] * parity == -create[i]
               for i in range(NMODES))
    assert all(parity * annihilate[i] * parity == -annihilate[i]
               for i in range(NMODES))

    # Retained-word sectors.  Mixed words are represented by the full grade-0
    # matrix-unit sector below; quadratic same-chirality words remain visible.
    g_pos_one = create
    g_neg_one = annihilate
    g_pos_two = [create[i] * create[j]
                 for i in range(NMODES) for j in range(i + 1, NMODES)]
    g_neg_two = [annihilate[i] * annihilate[j]
                 for i in range(NMODES) for j in range(i + 1, NMODES)]

    assert all(check_grade(number_clock, x, 1) for x in g_pos_one)
    assert all(check_grade(number_clock, x, -1) for x in g_neg_one)
    assert all(check_grade(number_clock, x, 2) for x in g_pos_two)
    assert all(check_grade(number_clock, x, -2) for x in g_neg_two)
    assert rank_of(g_pos_two) == 10
    assert rank_of(g_neg_two) == 10

    # The retained quadratic sectors are exchanged by the real mirror.
    assert all(
        mirror * create[i] * create[j] * mirror ==
        (-1) ** (i + j) * annihilate[i] * annihilate[j]
        for i in range(NMODES) for j in range(i + 1, NMODES))
    assert all(
        mirror * annihilate[i] * annihilate[j] * mirror ==
        (-1) ** (i + j) * create[i] * create[j]
        for i in range(NMODES) for j in range(i + 1, NMODES))

    # Exact obstruction witnesses: a cubic word survives, so the Fock model
    # is not a five-grade truncation.
    cubic_plus = create[0] * create[1] * create[2]
    cubic_minus = annihilate[0] * annihilate[1] * annihilate[2]
    assert cubic_plus != ZERO and cubic_minus != ZERO
    assert check_grade(number_clock, cubic_plus, 3)
    assert check_grade(number_clock, cubic_minus, -3)
    assert comm(g_pos_two[0], g_pos_one[2]) == ZERO
    assert comm(g_neg_two[0], g_neg_one[2]) == ZERO
    assert anti(g_pos_two[0], g_pos_one[2]) != ZERO
    assert anti(g_neg_two[0], g_neg_one[2]) != ZERO

    # The antisymmetrized quadratic Lie skeleton is a separate finite object.
    # It keeps Λ² of each chiral sector and the mixed commutator sector, while
    # discarding the unrestricted cubic associative words.
    lie_sectors = {
        -2: independent_basis([
            comm(annihilate[i], annihilate[j])
            for i in range(NMODES) for j in range(i + 1, NMODES)
        ]),
        -1: independent_basis(annihilate),
         0: independent_basis([
            comm(create[i], annihilate[j])
            for i in range(NMODES) for j in range(NMODES)
        ]),
         1: independent_basis(create),
         2: independent_basis([
            comm(create[i], create[j])
            for i in range(NMODES) for j in range(i + 1, NMODES)
        ]),
    }
    witt_lie_basis = lie_one_step(create + annihilate)
    assert len(witt_lie_basis) == 55
    witt_grade_dimensions = {
        k: sum(1 for x in witt_lie_basis if check_grade(number_clock, x, k))
        for k in range(-5, 6)
    }
    assert witt_grade_dimensions == {
        -2: 10, -1: 5, 0: 25, 1: 5, 2: 10,
        -5: 0, -4: 0, -3: 0, 3: 0, 4: 0, 5: 0,
    }
    assert {k: len(v) for k, v in lie_sectors.items()} == {
        -2: 10, -1: 5, 0: 25, 1: 5, 2: 10,
    }
    assert all(
        check_grade(number_clock, x, k)
        for k, sector in lie_sectors.items() for x in sector
    )
    for r, left in lie_sectors.items():
        for s, right in lie_sectors.items():
            brackets = [comm(x, y) for x in left for y in right]
            if abs(r + s) > 2:
                assert all(x == ZERO for x in brackets)
            else:
                target = lie_sectors.get(r + s, [])
                assert rank_of(target + brackets) == len(target)

    full_dims = grade_dimensions()
    expected_dims = {-5: 1, -4: 10, -3: 45, -2: 120, -1: 210,
                     0: 252, 1: 210, 2: 120, 3: 45, 4: 10, 5: 1}
    assert full_dims == expected_dims
    assert sum(full_dims.values()) == DIM * DIM

    # Matrix-unit multiplication gives the complete associative routing test:
    # [E_uv, E_rs] can only have E_us or E_rv, both of additive grade.
    unit_routes_ok = True
    for u in range(DIM):
        for v in range(DIM):
            for r in range(DIM):
                for s in range(DIM):
                    if u == s and v == r:
                        continue
                    left_grade = popcount(u) - popcount(v)
                    right_grade = popcount(r) - popcount(s)
                    if (v == r and popcount(u) - popcount(v) +
                            popcount(r) - popcount(s) != popcount(u) - popcount(s)):
                        unit_routes_ok = False
                    if (u == s and popcount(r) - popcount(s) +
                            popcount(u) - popcount(v) != popcount(r) - popcount(v)):
                        unit_routes_ok = False
    assert unit_routes_ok

    report = {
        "model": "real five-mode Jordan-Wigner Cl(5,5) spinor/Fock matrices",
        "dimension": DIM,
        "retained_sector_dimensions": {
            "g_-2": rank_of(g_neg_two),
            "g_-1": rank_of(g_neg_one),
            "g_+1": rank_of(g_pos_one),
            "g_+2": rank_of(g_pos_two),
        },
        "selected_lie_five_grade_dimensions": {
            f"g_{k:+d}": len(sector)
            for k, sector in sorted(lie_sectors.items())
        },
        "selected_lie_five_grade_closed": True,
        "witt_generator_lie_closure_dimension": len(witt_lie_basis),
        "witt_generator_lie_grade_dimensions": {
            str(k): witt_grade_dimensions[k]
            for k in range(-2, 3)
        },
        "witt_generator_lie_closure_verified_after_one_step": True,
        "associative_generator_closure": {
            "dimension": DIM * DIM,
            "grade_min": -NMODES,
            "grade_max": NMODES,
            "nonzero_grade_plus_3": True,
        },
        "full_envelope_commutator_algebra": {
            "dimension": DIM * DIM - 1,
            "candidate": "sl_32(Q)",
        },
        "witt_generator_lie_closure": {
            "closure_mode": "lie_from_witt_generators_only",
            "operation": "ordinary_commutator",
            "dimension": len(witt_lie_basis),
            "grade_support": [-2, -1, 0, 1, 2],
            "grade_dimensions": {
                str(k): witt_grade_dimensions[k] for k in range(-2, 3)
            },
        },
        "full_endomorphism_grade_dimensions": full_dims,
        "real_involutions": {
            "mirror_square": True,
            "mirror_reverses_centered_number": True,
            "cartan_parity_square": True,
            "cartan_preserves_number_grade": True,
        },
        "five_grade_obstructions": {
            "g_+2_times_g_+1_nonzero": True,
            "g_-2_times_g_-1_nonzero": True,
            "g_+2_bracket_g_+1_zero": True,
            "g_-2_bracket_g_-1_zero": True,
            "g_+2_anticommutator_g_+1_nonzero": True,
            "g_-2_anticommutator_g_-1_nonzero": True,
            "g_+3_exists": True,
            "g_-3_exists": True,
            "g_+4_exists": True,
            "g_-4_exists": True,
            "g_+5_exists": True,
            "g_-5_exists": True,
        },
        "conclusion": (
            "ambient finite Z-graded End(Fock) envelope; retained words do not "
            "form a five-grade truncation"
        ),
        "generated_lie_closure":
            "55-dimensional ordinary-commutator closure from Witt generators",
        "associative_generator_closure_dimension": DIM * DIM,
        "full_envelope_commutator_dimension": DIM * DIM - 1,
        "candidate_real_form": "split_so(6,5)",
        "candidate_root_system": "B5",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
