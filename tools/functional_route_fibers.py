"""Exact functional-route Drazin data and SVD-free power-support shells.

All scalar arithmetic is Fraction arithmetic. Graph analysis is O(n).
Applying all shells to n-by-d values costs O(k*n*d) arithmetic operations;
materializing all dense shells costs at least O(k*n*n) output entries.
These are executable identities, not a kernel proof of this Python program.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from operator import index
from typing import Iterator, Sequence

Scalar = int | float | str | Fraction
Table = tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True)
class RouteGeometry:
    route: tuple[int, ...]
    recurrent: tuple[int, ...]
    depth: tuple[int, ...]
    rho: tuple[int, ...]
    inverse_route: tuple[int, ...]
    peel_height: tuple[int, ...]
    entry_depth_counts: tuple[int, ...]
    shell_ranks: tuple[int, ...]
    cycle_count: int

    @property
    def n(self) -> int:
        return len(self.route)

    @property
    def index(self) -> int:
        """Minimal Drazin index, not nilpotency index of the ambient zero matrix."""
        return max(self.depth)


def analyze_route(route: Sequence[int]) -> RouteGeometry:
    """Kahn peeling and reverse DP; no matrices, inverses, or SVDs."""
    if not route:
        raise ValueError("The runtime interface requires a nonempty route.")
    try:
        f = tuple(index(x) for x in route)
    except TypeError as exc:
        raise ValueError("Route targets must be integers.") from exc
    n = len(f)
    if any(isinstance(x, bool) for x in route) or any(j < 0 or j >= n for j in f):
        raise ValueError("Targets must be indices in range(n), not booleans.")
    degree = [0] * n
    for j in f:
        degree[j] += 1
    queue = [i for i, d in enumerate(degree) if d == 0]
    height = [0] * n
    head = 0
    while head < len(queue):
        u = queue[head]
        head += 1
        v = f[u]
        height[v] = max(height[v], height[u] + 1)
        degree[v] -= 1
        if degree[v] == 0:
            queue.append(v)
    recurrent = tuple(i for i, d in enumerate(degree) if d > 0)
    inverse = [-1] * n
    for c in recurrent:
        inverse[f[c]] = c
    depth, rho = [0] * n, list(range(n))
    for u in reversed(queue):
        depth[u] = depth[f[u]] + 1
        rho[u] = inverse[rho[f[u]]]
    k = max(depth)
    node_counts, shell_ranks = [0] * k, [0] * k
    for u in queue:
        node_counts[depth[u] - 1] += 1
        shell_ranks[height[u]] += 1
    seen, cycles = set(), 0
    for c in recurrent:
        if c not in seen:
            cycles += 1
            u = c
            while u not in seen:
                seen.add(u)
                u = f[u]
    return RouteGeometry(f, recurrent, tuple(depth), tuple(rho),
                         tuple(inverse[rho[i]] for i in range(n)),
                         tuple(-1 if degree[i] > 0 else height[i] for i in range(n)),
                         tuple(node_counts), tuple(shell_ranks), cycles)


def table(values: Sequence[Sequence[Scalar]], n: int) -> Table:
    if len(values) != n or not values or not values[0]:
        raise ValueError("Values must have n nonempty rows.")
    d = len(values[0])
    if any(len(row) != d for row in values):
        raise ValueError("Values must be rectangular.")
    try:
        return tuple(tuple(Fraction(x) for x in row) for row in values)
    except (ValueError, TypeError, OverflowError, ZeroDivisionError) as exc:
        raise ValueError("Values must be finite rational-convertible scalars.") from exc


def identity(n: int) -> Table:
    return tuple(tuple(Fraction(i == j) for j in range(n)) for i in range(n))


def _zero(n: int, d: int) -> list[list[Fraction]]:
    return [[Fraction(0) for _ in range(d)] for _ in range(n)]


def _difference(a: Table, b: Table) -> Table:
    return tuple(tuple(x - y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))


def core_apply(g: RouteGeometry, values: Sequence[Sequence[Scalar]]) -> Table:
    v = table(values, g.n)
    return tuple(v[j] for j in g.rho)


def drazin_apply(g: RouteGeometry, values: Sequence[Sequence[Scalar]]) -> Table:
    v = table(values, g.n)
    return tuple(v[j] for j in g.inverse_route)


def core_operator_apply(g: RouteGeometry, values: Sequence[Sequence[Scalar]]) -> Table:
    """Apply C=A E, not E; they differ on nontrivial recurrent cycles."""
    v = table(values, g.n)
    return tuple(v[g.route[g.rho[i]]] for i in range(g.n))


def power_fibers(g: RouteGeometry, m: int) -> dict[int, list[int]]:
    """Fibers for N^m, m>=1. Computing this level alone costs O(m*n)."""
    if m < 1:
        raise ValueError("Positive powers only; N^0 is the ambient identity.")
    if m >= g.index:
        return {}
    ancestor = list(range(g.n))
    for _ in range(m):
        ancestor = [g.route[j] for j in ancestor]
    groups: dict[int, list[int]] = {}
    for i, j in enumerate(ancestor):
        if g.depth[i] > m:
            groups.setdefault(j, []).append(i)
    return groups


def _project(groups: dict[int, list[int]], v: Table) -> Table:
    out = _zero(len(v), len(v[0]))
    for members in groups.values():
        average = [sum((v[i][a] for i in members), Fraction(0)) / len(members)
                   for a in range(len(v[0]))]
        for i in members:
            out[i] = average.copy()
    return tuple(tuple(row) for row in out)


def power_range_apply(g: RouteGeometry, m: int,
                      values: Sequence[Sequence[Scalar]]) -> Table:
    """Apply (N^m)(N^m)^dagger without computing a pseudoinverse."""
    if m < 0:
        raise ValueError("Power must be nonnegative.")
    v = table(values, g.n)
    return v if m == 0 else _project(power_fibers(g, m), v)


def nilpotent_power_apply(g: RouteGeometry, m: int,
                          values: Sequence[Sequence[Scalar]]) -> Table:
    """Apply N^m; the m=0 convention is I, not the Drazin complement."""
    if m < 0:
        raise ValueError("Power must be nonnegative.")
    v = table(values, g.n)
    if m == 0:
        return v
    out = _zero(g.n, len(v[0]))
    for j, members in power_fibers(g, m).items():
        row = [v[j][a] - v[g.rho[j]][a] for a in range(len(v[0]))]
        for i in members:
            out[i] = row.copy()
    return tuple(tuple(row) for row in out)


def power_pinv_apply(g: RouteGeometry, m: int,
                     values: Sequence[Sequence[Scalar]]) -> Table:
    """Apply the actual ambient (N^m)^dagger using a full-rank factorization.

    For positive m, N^m=U B; U is fiber membership, B has rows e_j-e_rho(j).
    U^dagger is fiber averaging. B B^T has blocks I+11^T indexed by rho(j).
    Thus (N^m)^dagger=B^T(B B^T)^(-1)(U^T U)^(-1)U^T.
    This is not pseudoinverse transport through a nonorthogonal similarity.
    """
    if m < 0:
        raise ValueError("Power must be nonnegative.")
    v = table(values, g.n)
    if m == 0:
        return v
    groups = power_fibers(g, m)
    averages = {j: [sum((v[i][a] for i in members), Fraction(0)) / len(members)
                    for a in range(len(v[0]))] for j, members in groups.items()}
    by_anchor: dict[int, list[int]] = {}
    for j in groups:
        by_anchor.setdefault(g.rho[j], []).append(j)
    out = _zero(g.n, len(v[0]))
    for anchor, targets in by_anchor.items():
        correction = [sum((averages[j][a] for j in targets), Fraction(0)) /
                      (len(targets) + 1) for a in range(len(v[0]))]
        out[anchor] = [-x for x in correction]
        for j in targets:
            out[j] = [averages[j][a] - correction[a] for a in range(len(v[0]))]
    return tuple(tuple(row) for row in out)


def shell_actions(g: RouteGeometry,
                  values: Sequence[Sequence[Scalar]]) -> Iterator[Table]:
    """Yield S_m V in increasing m, with S_m=F(P_m-P_(m+1))F.

    O(k*n*d) arithmetic and O(n*d) working memory; consuming and storing all
    outputs requires O(k*n*d) memory. Rank-zero shells are not fabricated.
    """
    v = table(values, g.n)
    fv = _difference(v, tuple(v[j] for j in g.rho))
    previous = fv
    ancestor = list(range(g.n))
    for m in range(1, g.index + 1):
        ancestor = [g.route[j] for j in ancestor]
        groups: dict[int, list[int]] = {}
        for i, j in enumerate(ancestor):
            if g.depth[i] > m:
                groups.setdefault(j, []).append(i)
        current = _project(groups, fv)
        yield _difference(previous, current)
        previous = current


def dense_operators(g: RouteGeometry, max_n: int = 128) -> dict[str, object]:
    """Explicit exact matrices for small audits, never described as O(n)."""
    if g.n > max_n:
        raise ValueError("Dense output exceeds max_n; use operator application.")
    eye = identity(g.n)
    return {'A': tuple(eye[j] for j in g.route), 'E': core_apply(g, eye),
            'F': _difference(eye, core_apply(g, eye)),
            'D': drazin_apply(g, eye), 'C': core_operator_apply(g, eye),
            'N': nilpotent_power_apply(g, 1, eye),
            'shells': tuple(shell_actions(g, eye))}
