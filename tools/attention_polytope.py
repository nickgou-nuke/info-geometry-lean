"""Exact sparse convex decomposition of rectangular row-stochastic attention.

Each vertex chooses one key for each query; choices need not be permutations.
Uses Fraction arithmetic and never silently renormalizes or rounds the matrix.
The full product-weight expansion is a proof device, not the runtime algorithm.

CLI: python tools/attention_polytope.py input.json
Input: {"attention": [["1/2", "1/2"], ["1/4", "3/4"]],
        "values": [[1, 0], [0, 1]]}
Decimal JSON literals are parsed exactly as decimal fractions. Python float
arguments are interpreted as their exact binary values, so rounded softmax
rows may fail exact normalization. normalize_rows is an explicit separate step.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence, TypeAlias

Scalar: TypeAlias = int | float | str | Fraction
RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True)
class RoutingTerm:
    weight: Fraction
    route: tuple[int, ...]


def rational_matrix(matrix: Sequence[Sequence[Scalar]]) -> RationalMatrix:
    """Convert a finite nonempty rectangular matrix without normalization."""
    if not matrix or not matrix[0]:
        raise ValueError("The runtime interface requires at least one row and column.")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("Matrix rows must have the same length.")
    try:
        return tuple(tuple(Fraction(value) for value in row) for row in matrix)
    except (ValueError, TypeError, OverflowError, ZeroDivisionError) as exc:
        raise ValueError("Entries must be finite rational numbers.") from exc


def normalize_rows(matrix: Sequence[Sequence[Scalar]]) -> RationalMatrix:
    """Explicitly change a nonnegative matrix into one with unit row sums."""
    matrix = rational_matrix(matrix)
    result = []
    for row in matrix:
        if any(value < 0 for value in row) or sum(row) <= 0:
            raise ValueError("Every row must be nonnegative with positive total mass.")
        total = sum(row)
        result.append(tuple(value / total for value in row))
    return tuple(result)


def _attention(matrix: Sequence[Sequence[Scalar]]) -> RationalMatrix:
    matrix = rational_matrix(matrix)
    for row in matrix:
        if any(value < 0 for value in row):
            raise ValueError("Attention entries must be nonnegative.")
        if sum(row) != 1:
            raise ValueError("Row sums must equal one exactly; normalize explicitly.")
    return matrix


def reconstruct(terms: Sequence[RoutingTerm], rows: int, columns: int) -> RationalMatrix:
    """Reconstruct the attention matrix from a finite routing certificate."""
    if rows <= 0 or columns <= 0:
        raise ValueError("Matrix dimensions must be positive.")
    result = [[Fraction(0) for _ in range(columns)] for _ in range(rows)]
    for term in terms:
        if len(term.route) != rows:
            raise ValueError("Each route must have one key index for every query.")
        if term.weight < 0:
            raise ValueError("Convex coefficients must be nonnegative.")
        for i, j in enumerate(term.route):
            if not 0 <= j < columns:
                raise ValueError("Route key index is out of bounds.")
            result[i][j] += term.weight
    return tuple(tuple(row) for row in result)


def expected_causal_core_rank(matrix: Sequence[Sequence[Scalar]]) -> Fraction:
    """Expected recurrent core dimension for any exact causal route coupling.

    This is trace(P), not the Drazin rank of P itself. The mathematical identity
    is specified by Routing.CausalCoreTrace.causal_mixture_core_trace.
    No routes, powers, pseudoinverses, or spectra are computed. Dense validation
    costs O(n^2) entry checks; reduction costs O(n) additions (not a constant
    bit-cost claim for Fraction arithmetic).
    """
    matrix = _attention(matrix)
    size = len(matrix)
    if len(matrix[0]) != size:
        raise ValueError("Causal core diagnostics require square attention.")
    if any(matrix[i][j] != 0 for i in range(size) for j in range(i + 1, size)):
        raise ValueError("Causal core diagnostics require a lower-triangular mask.")
    return sum((matrix[i][i] for i in range(size)), Fraction(0))


def verify_certificate(matrix: Sequence[Sequence[Scalar]],
                       terms: Sequence[RoutingTerm]) -> bool:
    """Check mass, support, and reconstruction using exact rational arithmetic.

    This is a runtime certificate check, not a Lean kernel proof of this Python
    implementation. The companion Lean statements specify the matrix semantics.
    """
    matrix = _attention(matrix)
    rows, columns = len(matrix), len(matrix[0])
    if any(term.weight <= 0 for term in terms) or sum(t.weight for t in terms) != 1:
        return False
    try:
        if reconstruct(terms, rows, columns) != matrix:
            return False
    except (TypeError, ValueError):
        return False
    return all(matrix[i][j] > 0 for term in terms for i, j in enumerate(term.route))


def decompose(matrix: Sequence[Sequence[Scalar]]) -> tuple[RoutingTerm, ...]:
    """Greedy exact decomposition, at most nnz(A) - rows(A) + 1 routes.

    The residual has a common row mass r. Select one positive entry per row,
    subtract the smallest selected mass along that deterministic route, and
    continue. At least one positive entry disappears each step. In the final
    step at least one entry in every row disappears. No forbidden edge appears.
    The selection order is deterministic but the convex expansion is not unique.
    """
    matrix = _attention(matrix)
    residual = [list(row) for row in matrix]
    rows, columns = len(matrix), len(matrix[0])
    bound = sum(value > 0 for row in matrix for value in row) - rows + 1
    remaining = Fraction(1)
    result = []
    while remaining:
        route = tuple(next(j for j in range(columns) if residual[i][j] > 0)
                      for i in range(rows))
        weight = min(residual[i][j] for i, j in enumerate(route))
        result.append(RoutingTerm(weight, route))
        for i, j in enumerate(route):
            residual[i][j] -= weight
        remaining -= weight
        if len(result) > bound:
            raise ArithmeticError("Support-decrease invariant failed.")
        if any(sum(row) != remaining for row in residual):
            raise ArithmeticError("Common residual row-mass invariant failed.")
    terms = tuple(result)
    if not verify_certificate(matrix, terms):
        raise ArithmeticError("The resulting routing certificate failed validation.")
    return terms


def readout(matrix: Sequence[Sequence[Scalar]],
            values: Sequence[Sequence[Scalar]]) -> RationalMatrix:
    """Direct attention readout A V."""
    matrix, values = _attention(matrix), rational_matrix(values)
    if len(values) != len(matrix[0]):
        raise ValueError("The value table must have one row per key.")
    return tuple(tuple(sum((weight * values[j][k] for j, weight in enumerate(row)),
                           Fraction(0)) for k in range(len(values[0]))) for row in matrix)


def route_readout(terms: Sequence[RoutingTerm],
                  values: Sequence[Sequence[Scalar]]) -> RationalMatrix:
    """The same readout, calculated by weighted deterministic value gathers."""
    if not terms:
        raise ValueError("A normalized routing mixture cannot be empty.")
    values = rational_matrix(values)
    rows = len(terms[0].route)
    reconstruct(terms, rows, len(values))
    if sum(term.weight for term in terms) != 1:
        raise ValueError("Routing weights must sum to one.")
    return tuple(tuple(sum((term.weight * values[term.route[i]][k] for term in terms),
                           Fraction(0)) for k in range(len(values[0]))) for i in range(rows))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON attention matrix and optional values")
    parser.add_argument("--normalize-rows", action="store_true",
                        help="Explicitly normalize the input before decomposition")
    parser.add_argument("--causal-core-only", action="store_true",
                        help="Report expected causal core rank without decomposing routes")
    args = parser.parse_args()
    try:
        payload = json.loads(args.input.read_text(encoding="utf-8"), parse_float=Fraction)
        original = rational_matrix(payload["attention"])
        attention = normalize_rows(original) if args.normalize_rows else _attention(original)
        if args.causal_core_only:
            rank = expected_causal_core_rank(attention)
            print(json.dumps({
                "input_changed": attention != original,
                "rows": len(attention), "columns": len(attention[0]),
                "expected_causal_core_rank": str(rank),
                "expected_causal_core_fraction": str(rank / len(attention)),
                "route_decomposition_performed": False,
            }, indent=2))
            return
        terms = decompose(attention)
        result = {
            "input_changed": attention != original,
            "rows": len(attention), "columns": len(attention[0]),
            "number_of_routes": len(terms),
            "support_bound": sum(x > 0 for row in attention for x in row) - len(attention) + 1,
            "terms": [{"weight": str(t.weight), "route": list(t.route)} for t in terms],
            "exact_reconstruction": verify_certificate(attention, terms),
        }
        if "values" in payload:
            direct = readout(attention, payload["values"])
            routed = route_readout(terms, payload["values"])
            result["readout"] = [[str(x) for x in row] for row in routed]
            result["exact_readout_match"] = direct == routed
        print(json.dumps(result, indent=2))
    except (OSError, KeyError, TypeError, ValueError, ArithmeticError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
