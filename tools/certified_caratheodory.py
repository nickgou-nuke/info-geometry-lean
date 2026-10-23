"""Exact-rational, value-dependent Caratheodory pruning.

No numerical rank tolerance, clipping, normalization, or floating-point SVD is
used. Native Python floats are converted to their exact binary rational values;
JSON decimal literals are parsed as exact decimal fractions. Each result is
independently checked. This checker is Python code, not a Lean kernel check.

CLI: python tools/certified_caratheodory.py input.json
Input: {"values": [[0], [1], [2]], "weights": ["1/3", "1/3", "1/3"]}
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Sequence, TypeAlias

Scalar: TypeAlias = int | float | str | Fraction
Vector: TypeAlias = tuple[Fraction, ...]
Table: TypeAlias = tuple[Vector, ...]


@dataclass(frozen=True)
class Pivot:
    index: int
    step: Fraction
    direction: Vector


@dataclass(frozen=True)
class PruningResult:
    weights: Vector
    pivots: tuple[Pivot, ...]


def inputs(values: Sequence[Sequence[Scalar]], weights: Sequence[Scalar]) -> tuple[Table, Vector]:
    if not values or len(values) != len(weights):
        raise ValueError("Need one weight per key and at least one key.")
    dim = len(values[0])
    if any(len(row) != dim for row in values):
        raise ValueError("Values must be rectangular; zero-dimensional values are permitted.")
    try:
        v = tuple(tuple(Fraction(x) for x in row) for row in values)
        p = tuple(Fraction(x) for x in weights)
    except (TypeError, ValueError, OverflowError, ZeroDivisionError) as exc:
        raise ValueError("All entries must be finite rational-convertible scalars.") from exc
    if any(x < 0 for x in p) or sum(p) != 1:
        raise ValueError("Weights must be nonnegative and sum to one exactly.")
    return v, p


def homogeneous(values: Table, support: Sequence[int]) -> list[list[Fraction]]:
    return [[Fraction(1) for _ in support]] + [
        [values[j][d] for j in support] for d in range(len(values[0]))]


def rref(matrix: Sequence[Sequence[Fraction]]) -> tuple[list[list[Fraction]], tuple[int, ...]]:
    """Row reduction with exact field operations; no tolerance decisions."""
    a = [list(row) for row in matrix]
    if not a:
        return [], ()
    width = len(a[0])
    if any(len(row) != width for row in a):
        raise ValueError("RREF matrix must be rectangular.")
    pivots: list[int] = []
    r = 0
    for col in range(width):
        pivot = next((i for i in range(r, len(a)) if a[i][col] != 0), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        divisor = a[r][col]
        a[r] = [x / divisor for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col]:
                factor = a[i][col]
                a[i] = [x - factor * y for x, y in zip(a[i], a[r])]
        pivots.append(col)
        r += 1
        if r == len(a):
            break
    return a, tuple(pivots)


def kernel_direction(values: Table, support: Sequence[int]) -> Vector | None:
    """Return one nonzero homogeneous kernel direction, or certify full column rank."""
    a, pivots = rref(homogeneous(values, support))
    if len(pivots) == len(support):
        return None
    free = next(i for i in range(len(support)) if i not in pivots)
    local = [Fraction(0)] * len(support)
    local[free] = Fraction(1)
    for row, col in enumerate(pivots):
        local[col] = -a[row][free]
    result = [Fraction(0)] * len(values)
    for j, value in zip(support, local):
        result[j] = value
    return tuple(result)


def readout(values: Table, weights: Vector) -> Vector:
    return tuple(sum((weights[j] * values[j][d] for j in range(len(values))), Fraction(0))
                 for d in range(len(values[0])))


def verify_certificate(values: Sequence[Sequence[Scalar]], weights: Sequence[Scalar],
                       result: PruningResult) -> bool:
    """Replay, recheck exact invariants, and independently test final affine independence."""
    try:
        v, p = inputs(values, weights)
        if not isinstance(result, PruningResult) or not all(isinstance(x, Fraction) for x in result.weights):
            return False
        original = p
        target = readout(v, p)
        initial_support = {j for j, x in enumerate(p) if x > 0}
        if len(result.pivots) > len(initial_support) - 1:
            return False
        for pivot in result.pivots:
            if (not isinstance(pivot, Pivot) or not isinstance(pivot.step, Fraction)
                    or not isinstance(pivot.index, int)
                    or not all(isinstance(x, Fraction) for x in pivot.direction)):
                return False
            support = {j for j, x in enumerate(p) if x > 0}
            delta = pivot.direction
            if len(delta) != len(p) or not any(delta) or sum(delta) != 0:
                return False
            if any(delta[j] != 0 for j in range(len(p)) if j not in support):
                return False
            if any(readout(v, delta)):
                return False
            positive = [j for j in support if delta[j] > 0]
            if pivot.index not in positive or pivot.step <= 0:
                return False
            if pivot.step != p[pivot.index] / delta[pivot.index]:
                return False
            if pivot.step != min(p[j] / delta[j] for j in positive):
                return False
            q = tuple(x - pivot.step * z for x, z in zip(p, delta))
            next_support = {j for j, x in enumerate(q) if x > 0}
            if any(x < 0 for x in q) or sum(q) != 1 or q[pivot.index] != 0:
                return False
            if not next_support < support or readout(v, q) != target:
                return False
            p = q
        if result.weights != p or any(x < 0 for x in p) or sum(p) != 1:
            return False
        support = [j for j, x in enumerate(p) if x > 0]
        _, columns = rref(homogeneous(v, support))
        return (len(columns) == len(support) <= len(v[0]) + 1
                and set(support) <= initial_support and readout(v, p) == readout(v, original))
    except (ArithmeticError, TypeError, ValueError, IndexError, AttributeError):
        return False


def prune(values: Sequence[Sequence[Scalar]], weights: Sequence[Scalar]) -> PruningResult:
    v, p = inputs(values, weights)
    original = p
    limit = sum(x > 0 for x in p) - 1
    pivots: list[Pivot] = []
    while True:
        support = [j for j, x in enumerate(p) if x > 0]
        delta = kernel_direction(v, support)
        if delta is None:
            break
        positive = [j for j in support if delta[j] > 0]
        if not positive:
            raise ArithmeticError("Nonzero zero-mass direction lacks a positive coordinate.")
        j = min(positive, key=lambda i: (p[i] / delta[i], i))
        t = p[j] / delta[j]
        q = tuple(x - t * z for x, z in zip(p, delta))
        if t <= 0 or any(x < 0 for x in q) or sum(x > 0 for x in q) >= len(support):
            raise ArithmeticError("Exact minimum-ratio support invariant failed.")
        pivots.append(Pivot(j, t, delta))
        if len(pivots) > limit:
            raise ArithmeticError("Support-cardinality termination bound failed.")
        p = q
    result = PruningResult(p, tuple(pivots))
    if not verify_certificate(v, original, result):
        raise ArithmeticError("Independent pruning certificate check failed.")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    try:
        payload = json.loads(args.input.read_text(), parse_float=Fraction)
        v, p = inputs(payload["values"], payload["weights"])
        result = prune(v, p)
        print(json.dumps({
            "weights": [str(x) for x in result.weights],
            "support": [j for j, x in enumerate(result.weights) if x > 0],
            "readout": [str(x) for x in readout(v, result.weights)],
            "pivots": [{"index": s.index, "step": str(s.step),
                        "direction": [str(x) for x in s.direction]} for s in result.pivots],
            "exact_certificate_valid": verify_certificate(v, p, result),
            "kernel_verified": False,
        }, indent=2))
    except (OSError, KeyError, TypeError, ValueError, ArithmeticError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
