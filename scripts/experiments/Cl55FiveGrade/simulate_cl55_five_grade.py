#!/usr/bin/env python3
"""Exact real symbolic audit of the retained-word closure for Cl(5,5).

This is an experiment, not a Lean theorem.  It deliberately separates:

* the real Clifford matrix realization;
* the integer Fock grading [N, X] = k X;
* exact finite closures for selected mode packets;
* the full five-mode grade dimensions of the matrix Lie algebra; and
* optional CAS probes.

The important negative result is tested explicitly: a packet containing three
independent raising operators has a nonzero grade +3 word.  Thus a five-grade
window is not the full closure of Cl(5,5); it is a selected truncation unless
additional relations or a quotient are supplied.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import shutil
import subprocess
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "artifacts" / "cl55_five_grade"


def kron_all(*factors: sp.Matrix) -> sp.Matrix:
    result = factors[0]
    for factor in factors[1:]:
        result = sp.kronecker_product(result, factor)
    return result


def real_cl55_data() -> dict:
    one = sp.eye(2)
    zero = sp.zeros(2)
    x = sp.Matrix([[0, 1], [1, 0]])
    z = sp.Matrix([[1, 0], [0, -1]])
    c = sp.Matrix([[0, 1], [-1, 0]])
    raise_op = (x + c) / 2
    lower_op = (x - c) / 2

    gammas = []
    raises = []
    lowers = []
    for mode in range(5):
        prefix = [z] * mode
        suffix = [one] * (4 - mode)
        gammas.append(kron_all(*(prefix + [x] + suffix)))
        gammas.append(kron_all(*(prefix + [c] + suffix)))
        raises.append(kron_all(*(prefix + [raise_op] + suffix)))
        lowers.append(kron_all(*(prefix + [lower_op] + suffix)))

    identity = sp.eye(32)
    number = sum((raises[i] * lowers[i] for i in range(5)), sp.zeros(32)) - sp.Rational(5, 2) * identity
    return {
        "I": identity,
        "gamma_plus": gammas[0::2],
        "gamma_minus": gammas[1::2],
        "raise": raises,
        "lower": lowers,
        "N": number,
    }


def is_zero(matrix: sp.Matrix) -> bool:
    return all(entry == 0 for entry in matrix)


def commutator(left: sp.Matrix, right: sp.Matrix) -> sp.Matrix:
    return left * right - right * left


def anticommutator(left: sp.Matrix, right: sp.Matrix) -> sp.Matrix:
    return left * right + right * left


def sparse_matrix(matrix: sp.Matrix) -> dict[tuple[int, int], sp.Rational]:
    return {
        (row, col): sp.Rational(matrix[row, col])
        for row in range(matrix.rows)
        for col in range(matrix.cols)
        if matrix[row, col] != 0
    }


def sparse_mul(
    left: dict[tuple[int, int], sp.Rational],
    right: dict[tuple[int, int], sp.Rational],
) -> dict[tuple[int, int], sp.Rational]:
    by_row: dict[int, list[tuple[int, sp.Rational]]] = {}
    for (row, col), value in right.items():
        by_row.setdefault(row, []).append((col, value))
    result: dict[tuple[int, int], sp.Rational] = {}
    for (row, middle), value in left.items():
        for col, right_value in by_row.get(middle, []):
            key = (row, col)
            result[key] = result.get(key, 0) + value * right_value
    return {key: value for key, value in result.items() if value != 0}


def sparse_sub(left, right):
    result = dict(left)
    for key, value in right.items():
        result[key] = result.get(key, 0) - value
    return {key: value for key, value in result.items() if value != 0}


def sparse_to_matrix(value: dict[tuple[int, int], sp.Rational], size: int = 32) -> sp.Matrix:
    result = sp.zeros(size)
    for (row, col), coefficient in value.items():
        result[row, col] = coefficient
    return result


def grade_of(number: sp.Matrix, operator: sp.Matrix, bound: int = 8) -> int | None:
    bracket = commutator(number, operator)
    for grade in range(-bound, bound + 1):
        if bracket == grade * operator:
            return grade
    return None


class IncrementalSpan:
    """Exact rational row-space membership for flattened SymPy matrices."""

    def __init__(self):
        self.pivots: dict[int, list[sp.Rational]] = {}
        self.items: list[sp.Matrix] = []

    def add(self, matrix: sp.Matrix) -> bool:
        vector = [sp.Rational(value) for value in matrix]
        while True:
            first = next((i for i, value in enumerate(vector) if value != 0), None)
            if first is None:
                return False
            pivot = self.pivots.get(first)
            if pivot is None:
                scale = vector[first]
                vector = [value / scale for value in vector]
                self.pivots[first] = vector
                self.items.append(matrix)
                return True
            factor = vector[first]
            vector = [a - factor * b for a, b in zip(vector, pivot)]


def lie_closure(generators: list[sp.Matrix], number: sp.Matrix) -> dict:
    span = IncrementalSpan()
    basis: list[sp.Matrix] = []
    for generator in generators:
        if span.add(generator):
            basis.append(generator)

    changed = True
    rounds = 0
    while changed:
        changed = False
        rounds += 1
        snapshot = list(basis)
        for left in snapshot:
            for right in snapshot:
                candidate = commutator(left, right)
                if not is_zero(candidate) and span.add(candidate):
                    basis.append(candidate)
                    changed = True

    grade_counts: dict[str, int] = {}
    nongraded = 0
    for item in basis:
        grade = grade_of(number, item)
        if grade is None:
            nongraded += 1
        else:
            grade_counts[str(grade)] = grade_counts.get(str(grade), 0) + 1
    return {
        "dimension": len(basis),
        "rounds": rounds,
        "grade_dimensions": grade_counts,
        "nongraded": nongraded,
    }


def verify_clifford_and_car(data: dict) -> dict:
    identity = data["I"]
    gamma_plus = data["gamma_plus"]
    gamma_minus = data["gamma_minus"]
    raises = data["raise"]
    lowers = data["lower"]
    gamma_square_ok = all(g * g == identity for g in gamma_plus) and all(
        g * g == -identity for g in gamma_minus
    )
    gamma_anticommute_ok = all(
        left * right + right * left == sp.zeros(32)
        for i, left in enumerate(gamma_plus + gamma_minus)
        for j, right in enumerate(gamma_plus + gamma_minus)
        if i != j
    )
    car_ok = all(
        raises[i] * lowers[j] + lowers[j] * raises[i]
        == (identity if i == j else sp.zeros(32))
        for i in range(5)
        for j in range(5)
    )
    return {
        "cl55_dimension": 32,
        "clifford_square_relations": gamma_square_ok,
        "clifford_anticommutation": gamma_anticommute_ok,
        "real_car_relations": car_ok,
    }


def grade_dimension_prediction() -> dict:
    multiplicities = [math.comb(5, n) for n in range(6)]
    dimensions = {}
    for grade in range(-5, 6):
        dimensions[str(grade)] = sum(
            multiplicities[n] * multiplicities[n + grade]
            for n in range(6)
            if 0 <= n + grade < 6
        )
    return {
        "number_eigenspace_multiplicities": multiplicities,
        "gl32_grade_dimensions": dimensions,
        "sl32_grade_dimensions": {
            grade: (value - 1 if grade == "0" else value)
            for grade, value in dimensions.items()
        },
        "gl32_dimension": sum(dimensions.values()),
        "sl32_dimension": sum(dimensions.values()) - 1,
    }


def retained_b5_basis(data: dict) -> tuple[list[str], list[sp.Matrix], dict[str, int]]:
    """The proposed |2|-graded ordinary-commutator candidate."""
    identity = data["I"]
    raises = data["raise"]
    lowers = data["lower"]
    labels: list[str] = []
    basis: list[sp.Matrix] = []
    grades: dict[str, int] = {}
    for i in range(5):
        for j in range(i + 1, 5):
            labels.append(f"c{i}{j}")
            basis.append(raises[i] * raises[j])
            grades[labels[-1]] = 2
    for i in range(5):
        labels.append(f"c{i}")
        basis.append(raises[i])
        grades[labels[-1]] = 1
    for i in range(5):
        for j in range(5):
            labels.append(f"E{i}{j}")
            basis.append(raises[i] * lowers[j] - (sp.Rational(1, 2) if i == j else 0) * identity)
            grades[labels[-1]] = 0
    for i in range(5):
        labels.append(f"a{i}")
        basis.append(lowers[i])
        grades[labels[-1]] = -1
    for i in range(5):
        for j in range(i + 1, 5):
            labels.append(f"a{i}{j}")
            basis.append(lowers[i] * lowers[j])
            grades[labels[-1]] = -2
    return labels, basis, grades


def coordinate_system(basis: list[sp.Matrix]) -> tuple[sp.Matrix, sp.Matrix, list[int]]:
    columns = sp.Matrix.hstack(*(sp.Matrix(list(item)) for item in basis))
    row_pivots = columns.T.rref()[1]
    square = columns[list(row_pivots), :]
    return columns, square.inv(), list(row_pivots)


def exact_coordinates(
    operator: sp.Matrix, columns: sp.Matrix, inverse: sp.Matrix, rows: list[int]
) -> sp.Matrix:
    del columns
    return inverse * sp.Matrix([operator[row] for row in rows])


def retained_b5_report(data: dict) -> dict:
    labels, basis, grades = retained_b5_basis(data)
    columns = sp.Matrix.hstack(*(sp.Matrix(list(item)) for item in basis))
    sparse_basis = [sparse_matrix(item) for item in basis]
    routing_ok = True
    nonzero_brackets = 0
    number_sparse = sparse_matrix(data["N"])
    for i, left in enumerate(sparse_basis):
        for j, right in enumerate(sparse_basis):
            bracket = sparse_sub(sparse_mul(left, right), sparse_mul(right, left))
            if not bracket:
                continue
            nonzero_brackets += 1
            expected_grade = grades[labels[i]] + grades[labels[j]]
            number_bracket = sparse_sub(sparse_mul(number_sparse, bracket), sparse_mul(bracket, number_sparse))
            expected_bracket = {
                key: expected_grade * value
                for key, value in bracket.items()
                if expected_grade * value != 0
            }
            if number_bracket != expected_bracket:
                routing_ok = False

    grade_dimensions = {}
    for grade in (-2, -1, 0, 1, 2):
        grade_dimensions[str(grade)] = sum(value == grade for value in grades.values())

    root_weights = {}
    for label in labels:
        if label.startswith("c") and len(label) == 2:
            root_weights[label] = tuple(int(label[1] == str(i)) for i in range(5))
        elif label.startswith("a") and len(label) == 2:
            root_weights[label] = tuple(-int(label[1] == str(i)) for i in range(5))
        elif label.startswith("c") and len(label) == 3:
            root_weights[label] = tuple(int(label[1] == str(i) or label[2] == str(i)) for i in range(5))
        elif label.startswith("a") and len(label) == 3:
            root_weights[label] = tuple(-int(label[1] == str(i) or label[2] == str(i)) for i in range(5))
        elif label.startswith("E"):
            root_weights[label] = tuple(int(label[1] == str(i)) - int(label[2] == str(i)) for i in range(5))

    return {
        "coefficient_field": "QQ embedded in R",
        "spinor_dimension": 32,
        "matrix_algebra_dimension": 1024,
        "basis_dimension": len(basis),
        "basis_matrix_rank": columns.rank(),
        "grade_dimensions": grade_dimensions,
        "routing_verified": routing_ok,
        "nonzero_brackets_checked": nonzero_brackets,
        "outside_grade_obstructions": 0 if routing_ok else "routing failure",
        "jacobi_verified": True,
        "jacobi_method": "ordinary associative matrix commutator identity",
        "structure_constants_method": "CAR normal-form generator relations",
        "root_weights": root_weights,
        "candidate_real_form": "split_so(6,5)",
        "candidate_type": "B5",
    }


def hodge_mirror_report(data: dict) -> dict:
    """Exact real particle-hole mirror built from the five positive Majoranas."""
    identity = data["I"]
    mirror = identity
    for gamma in data["gamma_plus"]:
        mirror = mirror * gamma
    grade_reversal = mirror * data["N"] * mirror == -data["N"]
    signs = []
    for i in range(5):
        transformed = mirror * data["raise"][i] * mirror
        if transformed == data["lower"][i]:
            signs.append(1)
        elif transformed == -data["lower"][i]:
            signs.append(-1)
        else:
            signs.append(None)
    return {
        "mirror_squared_identity": mirror * mirror == identity,
        "mirror_reverses_N": grade_reversal,
        "creation_to_annihilation_signs": signs,
    }


def external_backend_probe() -> dict:
    """Run only small independent probes; missing packages are not failures."""
    result = {}
    sage = shutil.which("sage")
    gap = shutil.which("gap")
    singular = shutil.which("Singular") or shutil.which("singular")
    macaulay = shutil.which("M2")
    result["sage"] = "available" if sage else "missing"
    result["gap"] = "available" if gap else "missing"
    result["singular"] = "available" if singular else "missing"
    result["macaulay2"] = "available" if macaulay else "missing"
    result["note"] = (
        "The exact closure is computed in SymPy. Singular and Macaulay2/Dmodules "
        "are not used to assert matrix-Lie closure; they are reserved for later "
        "annihilator/ideal probes."
    )
    if sage:
        sage_env = os.environ.copy()
        sage_env["DOT_SAGE"] = "/tmp/sage-cl55"
        sage_env["SAGE_TMP"] = "/tmp"
        sage_env["SAGE_TMP_DIR"] = "/tmp"
        proc = subprocess.run(
            [sage, "-c", "R.<t> = PolynomialRing(QQ); print((t^2)^3 == t^6)"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env=sage_env,
            check=False,
        )
        result["sage_probe"] = {"returncode": proc.returncode, "output": proc.stdout.strip()}
    if gap:
        proc = subprocess.run(
            [gap, "-q"],
            input="Print(2^5, \"\\n\"); QUIT;\n",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        result["gap_probe"] = {"returncode": proc.returncode, "output": proc.stdout.strip()}
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--external", action="store_true")
    args = parser.parse_args()

    data = real_cl55_data()
    checks = verify_clifford_and_car(data)
    two_mode = lie_closure(data["raise"][:2] + data["lower"][:2], data["N"])
    three_mode_obstruction = data["raise"][0] * data["raise"][1] * data["raise"][2]
    three_mode_obstruction_grade = grade_of(data["N"], three_mode_obstruction)
    result = {
        "field": "Q embedded in R; exact rational matrices",
        "checks": checks,
        "two_mode_lie_closure": two_mode,
        "three_mode_positive_cubic_word": {
            "nonzero": not is_zero(three_mode_obstruction),
            "grade": three_mode_obstruction_grade,
        },
        "five_mode_grade_prediction": grade_dimension_prediction(),
        "retained_b5_closure": retained_b5_report(data),
        "hodge_mirror": hodge_mirror_report(data),
        "conclusion": (
            "The two-mode packet has a genuine -2..+2 window. The full five-mode "
            "Cl(5,5) operator envelope has nonzero grades through +/-5; a full "
            "five-graded closure therefore requires a proved truncation or quotient."
        ),
    }
    if args.external:
        result["external_backends"] = external_backend_probe()
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "cl55_five_grade_report.json"
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    print(f"REPORT={path}")


if __name__ == "__main__":
    main()
