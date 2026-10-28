#!/usr/bin/env python3
"""Exact sparse Hodge analysis of a repository-evolution commit export.

The carrier is the *unfilled graph 1-complex*, with one vertex per commit
record (plus explicitly reported missing-parent boundary vertices), and one
oriented edge per recorded parent.  This does not infer declaration phylogeny,
fill triangles, estimate eigenvalues, or compile any Lean theorem.

Run:
    python ancestry_hodge.py --input phylogeny.json --out hodge.json \
        --witness-out hodge-cycles.json

Dependencies: numpy and scipy.  All matrix identities use sparse int64
arithmetic; no dense matrix or floating-point rank/eigensolver is used.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np
from scipy import sparse


REPORT_SCHEMA = "ancestry-hodge/v1"
WITNESS_SCHEMA = "ancestry-hodge-cycles/v1"
INTEGER_DTYPE = np.int64


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    parent_index: int


@dataclass
class Graph:
    vertices: list[str]
    edges: list[Edge]
    records: dict[str, dict[str, Any]]
    boundary_vertices: set[str]
    synthesized_boundary_vertices: set[str]

    @property
    def n(self) -> int:
        return len(self.vertices)

    @property
    def m(self) -> int:
        return len(self.edges)


class _UnionFind:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, u: int) -> int:
        while self.parent[u] != u:
            self.parent[u] = self.parent[self.parent[u]]
            u = self.parent[u]
        return u

    def union(self, u: int, v: int) -> bool:
        u, v = self.find(u), self.find(v)
        if u == v:
            return False
        if self.size[u] < self.size[v]:
            u, v = v, u
        self.parent[v] = u
        self.size[u] += self.size[v]
        return True


@dataclass
class Forest:
    edge_indices: list[int]
    nonforest_edge_indices: list[int]
    roots: list[int]
    parent: list[int]
    parent_edge: list[int]
    depth: list[int]
    component: list[int]
    # Parents precede children. Matching columns are each child's parent edge.
    nonroot_order: list[int]

    @property
    def components(self) -> int:
        return len(self.roots)


@dataclass
class Cycle:
    pivot_edge_index: int
    # The pivot is +1; the following signed forest edges close the walk.
    signed_edges: list[tuple[int, int]]


@dataclass
class Analysis:
    graph: Graph
    forest: Forest
    cycles: list[Cycle]
    B: sparse.csr_matrix
    D: sparse.csr_matrix
    Gamma: sparse.csr_matrix
    Z: sparse.csr_matrix
    report: dict[str, Any]

    def witness(self) -> dict[str, Any]:
        """A reconstructible sparse integer cycle-basis certificate."""
        return {
            "schema": WITNESS_SCHEMA,
            "source_sha256": self.report["source"]["sha256"],
            "complex": "unfilled oriented graph 1-complex",
            "encoding": {
                "vertices": "vertices[i] is the SHA/identifier of vertex i",
                "edges": (
                    "edges[j] = [source_vertex_index, target_vertex_index, "
                    "parent_index]; parent_index is zero-based"
                ),
                "incidence": "B[source,j]=-1; B[target,j]+=1 (self-loops cancel)",
                "signed_edges": "[edge_index, coefficient], coefficient in {-1,+1}",
                "columns": "cycles[k] encodes column k of Z",
            },
            "vertices": self.graph.vertices,
            "boundary_vertices": sorted(self.graph.boundary_vertices),
            "edges": [
                [e.source, e.target, e.parent_index] for e in self.graph.edges
            ],
            "forest_edge_indices": self.forest.edge_indices,
            "component_roots": self.forest.roots,
            "rank_minor": {
                "vertex_rows": self.forest.nonroot_order,
                "edge_columns": [
                    self.forest.parent_edge[v] for v in self.forest.nonroot_order
                ],
                "property": "upper triangular with diagonal entries +1 or -1",
            },
            "cycles": [
                {
                    "cycle_index": i,
                    "pivot": edge_descriptor(self.graph, cycle.pivot_edge_index),
                    "signed_edges": [[j, s] for j, s in cycle.signed_edges],
                }
                for i, cycle in enumerate(self.cycles)
            ],
            "checks": {
                key: self.report["checks"][key]
                for key in (
                    "B_times_Z_is_zero",
                    "cycle_pivot_submatrix_is_identity",
                    "forest_minor_is_upper_triangular",
                    "forest_minor_has_unit_absolute_diagonal",
                    "component_indicators_are_in_kernel_B_transpose",
                    "cycle_count_matches_nullity",
                )
            },
        }


def graph_from_export(data: Mapping[str, Any]) -> Graph:
    """Use complete `commits`, never the display-compressed `nodes`/`links`."""
    rows = data.get("commits")
    if not isinstance(rows, list):
        raise ValueError("Input must contain a 'commits' array; display nodes are insufficient")
    records: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("Every commit record must be an object")
        sha = row.get("sha")
        if not isinstance(sha, str) or not sha:
            raise ValueError("Every commit must have a nonempty string 'sha'")
        if sha in records:
            raise ValueError(f"Duplicate commit record: {sha}")
        parents = row.get("parents")
        if not isinstance(parents, list) or any(
            not isinstance(p, str) or not p for p in parents
        ):
            raise ValueError(f"Commit {sha} must have a list of nonempty parent identifiers")
        records[sha] = dict(row)

    missing = {
        p for row in records.values() for p in row["parents"] if p not in records
    }
    vertices = list(records) + sorted(missing)
    vertex_index = {sha: i for i, sha in enumerate(vertices)}
    edges = [
        Edge(vertex_index[parent], vertex_index[sha], parent_index)
        for sha, row in records.items()
        for parent_index, parent in enumerate(row["parents"])
    ]
    boundary = missing | {
        sha for sha, row in records.items() if bool(row.get("boundary", False))
    }
    # Integer products below are bounded by a small multiple of the number of
    # incidences, because B and Z have entries in {-1,0,+1}. Refuse theoretical
    # overflow rather than silently switching to floating point.
    if len(vertices) + 4 * len(edges) > np.iinfo(INTEGER_DTYPE).max:
        raise OverflowError("Graph exceeds the exact int64 arithmetic bound")
    return Graph(vertices, edges, records, boundary, missing)


def incidence_matrix(graph: Graph) -> sparse.csr_matrix:
    """B has shape V×E; each oriented parent→child column is -parent+child."""
    if not graph.edges:
        return sparse.csr_matrix((graph.n, 0), dtype=INTEGER_DTYPE)
    edge_indices = np.arange(graph.m, dtype=INTEGER_DTYPE)
    rows = np.array(
        [e.source for e in graph.edges] + [e.target for e in graph.edges],
        dtype=INTEGER_DTYPE,
    )
    cols = np.concatenate((edge_indices, edge_indices))
    values = np.concatenate(
        (-np.ones(graph.m, dtype=INTEGER_DTYPE), np.ones(graph.m, dtype=INTEGER_DTYPE))
    )
    B = sparse.coo_matrix(
        (values, (rows, cols)), shape=(graph.n, graph.m), dtype=INTEGER_DTYPE
    ).tocsr()
    B.sum_duplicates()
    B.eliminate_zeros()
    return B


def spanning_forest(graph: Graph) -> Forest:
    """Prefer first-parent edges, then union any still-disconnected endpoints."""
    uf = _UnionFind(graph.n)
    preferred = [i for i, e in enumerate(graph.edges) if e.parent_index == 0]
    remaining = [i for i, e in enumerate(graph.edges) if e.parent_index != 0]
    chosen = []
    for i in preferred + remaining:
        e = graph.edges[i]
        if uf.union(e.source, e.target):
            chosen.append(i)
    chosen_set = set(chosen)
    nonforest = [i for i in range(graph.m) if i not in chosen_set]
    adjacency: list[list[tuple[int, int]]] = [[] for _ in graph.vertices]
    for i in chosen:
        e = graph.edges[i]
        adjacency[e.source].append((e.target, i))
        adjacency[e.target].append((e.source, i))

    parent = [-1] * graph.n
    parent_edge = [-1] * graph.n
    depth = [0] * graph.n
    component = [-1] * graph.n
    roots: list[int] = []
    nonroot_order: list[int] = []
    for root in range(graph.n):
        if component[root] != -1:
            continue
        component[root] = len(roots)
        roots.append(root)
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, edge_index in adjacency[u]:
                if component[v] != -1:
                    continue
                parent[v] = u
                parent_edge[v] = edge_index
                depth[v] = depth[u] + 1
                component[v] = component[u]
                nonroot_order.append(v)
                queue.append(v)
    return Forest(chosen, nonforest, roots, parent, parent_edge, depth, component, nonroot_order)


def _traversal_sign(graph: Graph, edge_index: int, source: int, target: int) -> int:
    e = graph.edges[edge_index]
    if (e.source, e.target) == (source, target):
        return 1
    if (e.source, e.target) == (target, source):
        return -1
    raise ValueError("Requested traversal is not incident to this edge")


def fundamental_cycles(graph: Graph, forest: Forest) -> tuple[list[Cycle], sparse.csr_matrix]:
    """Each nonforest edge closes its unique forest path with coefficient +1."""
    cycles: list[Cycle] = []
    z_rows: list[int] = []
    z_cols: list[int] = []
    z_values: list[int] = []
    for cycle_index, pivot in enumerate(forest.nonforest_edge_indices):
        edge = graph.edges[pivot]
        # Pivot traverses u→v, so the forest portion must traverse v→u.
        a, b = edge.target, edge.source
        if forest.component[a] != forest.component[b]:
            raise ValueError("Nonforest edge endpoints belong to different components")
        left: list[tuple[int, int]] = []
        right: list[tuple[int, int]] = []
        while a != b:
            if forest.depth[a] >= forest.depth[b]:
                p, j = forest.parent[a], forest.parent_edge[a]
                left.append((j, _traversal_sign(graph, j, a, p)))
                a = p
            else:
                p, j = forest.parent[b], forest.parent_edge[b]
                right.append((j, _traversal_sign(graph, j, p, b)))
                b = p
        signed = [(pivot, 1)] + left + list(reversed(right))
        cycles.append(Cycle(pivot, signed))
        for j, sign in signed:
            z_rows.append(j)
            z_cols.append(cycle_index)
            z_values.append(sign)
    Z = sparse.coo_matrix(
        (np.asarray(z_values, dtype=INTEGER_DTYPE), (z_rows, z_cols)),
        shape=(graph.m, len(cycles)),
        dtype=INTEGER_DTYPE,
    ).tocsr()
    Z.sum_duplicates()
    Z.eliminate_zeros()
    return cycles, Z


def _is_zero(matrix: sparse.spmatrix) -> bool:
    matrix = matrix.tocsr(copy=True)
    matrix.eliminate_zeros()
    return matrix.nnz == 0


def _equal(left: sparse.spmatrix, right: sparse.spmatrix) -> bool:
    return left.shape == right.shape and _is_zero(left - right)


def edge_descriptor(graph: Graph, edge_index: int) -> dict[str, Any]:
    e = graph.edges[edge_index]
    return {
        "edge_index": edge_index,
        "source": graph.vertices[e.source],
        "target": graph.vertices[e.target],
        "parent_index": e.parent_index,
    }


def cycle_descriptor(graph: Graph, cycle: Cycle, cycle_index: int) -> dict[str, Any]:
    start = graph.edges[cycle.pivot_edge_index].source
    walk = [start]
    edges = []
    for j, sign in cycle.signed_edges:
        e = graph.edges[j]
        u, v = (e.source, e.target) if sign == 1 else (e.target, e.source)
        if u != walk[-1]:
            raise ValueError("Fundamental-cycle witness does not form a contiguous walk")
        walk.append(v)
        edges.append({**edge_descriptor(graph, j), "sign": sign})
    if walk[-1] != walk[0]:
        raise ValueError("Fundamental-cycle witness is not closed")
    return {
        "cycle_index": cycle_index,
        "pivot": edge_descriptor(graph, cycle.pivot_edge_index),
        "edge_count": len(cycle.signed_edges),
        "edge_ids": [j for j, _ in cycle.signed_edges],
        "signed_edges": [[j, sign] for j, sign in cycle.signed_edges],
        "edges": edges,
        "vertices": [graph.vertices[v] for v in walk],
        "closed_walk": True,
        "interpretation": "undirected cycle with signed oriented edges; not necessarily a directed cycle",
    }


def _directed_structure(graph: Graph) -> tuple[list[int], list[int], bool]:
    incoming = [0] * graph.n
    outgoing = [0] * graph.n
    forward: list[list[int]] = [[] for _ in graph.vertices]
    for e in graph.edges:
        incoming[e.target] += 1
        outgoing[e.source] += 1
        forward[e.source].append(e.target)
    pending = incoming.copy()
    queue = deque(i for i, count in enumerate(pending) if count == 0)
    visited = 0
    while queue:
        u = queue.popleft()
        visited += 1
        for v in forward[u]:
            pending[v] -= 1
            if pending[v] == 0:
                queue.append(v)
    return incoming, outgoing, visited == graph.n


def causal_cone(data: Mapping[str, Any] | Graph, sha: str, direction: str) -> set[str]:
    """Directed reachability, excluding the seed; separate from d and d*.

    `past` follows child→parent; `future` follows parent→child.  This works
    even for cyclic fixtures and does not assume chirality encodes time.
    """
    if direction not in {"past", "future"}:
        raise ValueError("direction must be 'past' or 'future'")
    graph = data if isinstance(data, Graph) else graph_from_export(data)
    indices = {s: i for i, s in enumerate(graph.vertices)}
    if sha not in indices:
        raise KeyError(sha)
    adjacency: list[list[int]] = [[] for _ in graph.vertices]
    for edge in graph.edges:
        u, v = (edge.source, edge.target) if direction == "future" else (edge.target, edge.source)
        adjacency[u].append(v)
    seed = indices[sha]
    seen = {seed}
    queue = deque([seed])
    while queue:
        for v in adjacency[queue.popleft()]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    seen.remove(seed)
    return {graph.vertices[i] for i in seen}


def analyze_export(
    data: Mapping[str, Any],
    *,
    source_path: str | None = None,
    source_sha256: str | None = None,
) -> Analysis:
    """Construct the actual sparse operators and verify exact certificates."""
    graph = graph_from_export(data)
    forest = spanning_forest(graph)
    B = incidence_matrix(graph)
    cycles, Z = fundamental_cycles(graph, forest)
    n, m, c = graph.n, graph.m, forest.components
    D = sparse.bmat(
        [[sparse.csr_matrix((n, n), dtype=INTEGER_DTYPE), B],
         [B.T, sparse.csr_matrix((m, m), dtype=INTEGER_DTYPE)]],
        format="csr", dtype=INTEGER_DTYPE,
    )
    signs = np.concatenate(
        (np.ones(n, dtype=INTEGER_DTYPE), -np.ones(m, dtype=INTEGER_DTYPE))
    )
    Gamma = (
        sparse.diags(signs, format="csr", dtype=INTEGER_DTYPE)
        if n + m else sparse.csr_matrix((0, 0), dtype=INTEGER_DTYPE)
    )
    L0 = (B @ B.T).tocsr()
    L1 = (B.T @ B).tocsr()
    commutator = (Gamma @ D - D @ Gamma).tocsr()
    commutator.eliminate_zeros()

    component_indicators = sparse.coo_matrix(
        (np.ones(n, dtype=INTEGER_DTYPE), (np.arange(n), forest.component)),
        shape=(n, c), dtype=INTEGER_DTYPE,
    ).tocsr()
    minor_columns = [forest.parent_edge[v] for v in forest.nonroot_order]
    minor = B[forest.nonroot_order, :][:, minor_columns]
    pivots = Z[forest.nonforest_edge_indices, :]
    expected_b1 = m - n + c
    checks = {
        "integer_arithmetic": B.dtype == D.dtype == Gamma.dtype == Z.dtype == np.dtype(INTEGER_DTYPE),
        "D_is_symmetric": _equal(D, D.T),
        "Gamma_squared_is_identity": _equal(Gamma @ Gamma, sparse.eye(n + m, dtype=INTEGER_DTYPE, format="csr")),
        "Gamma_D_plus_D_Gamma_is_zero": _is_zero(Gamma @ D + D @ Gamma),
        "D_squared_is_block_laplacian": _equal(D @ D, sparse.block_diag((L0, L1), format="csr")),
        "commutator_is_nonzero_iff_incidence_is_nonzero": (commutator.nnz > 0) == (B.nnz > 0),
        "B_times_Z_is_zero": _is_zero(B @ Z),
        "cycle_pivot_submatrix_is_identity": _equal(pivots, sparse.eye(len(cycles), dtype=INTEGER_DTYPE, format="csr")),
        "forest_edge_count_is_n_minus_components": len(forest.edge_indices) == n - c,
        "forest_minor_is_upper_triangular": _is_zero(sparse.tril(minor, k=-1)),
        "forest_minor_has_unit_absolute_diagonal": minor.shape == (n - c, n - c) and bool(np.all(np.abs(minor.diagonal()) == 1)),
        "component_indicators_are_in_kernel_B_transpose": _is_zero(B.T @ component_indicators),
        "component_indicators_partition_vertices": component_indicators.nnz == n and all(0 <= k < c for k in forest.component) and len(set(forest.component)) == c,
        "cycle_count_matches_nullity": len(cycles) == expected_b1,
        "cycle_coefficients_are_signed_units": bool(np.all(np.abs(Z.data) == 1)),
    }
    checks = {key: bool(value) for key, value in checks.items()}
    if not all(checks.values()):
        failed = ", ".join(key for key, value in checks.items() if not value)
        raise AssertionError(f"Exact Hodge/cycle certificate failed: {failed}")

    incoming, outgoing, is_dag = _directed_structure(graph)
    energies = [int(x) for x in L0.diagonal()]

    def vertex_description(i: int) -> dict[str, Any]:
        sha = graph.vertices[i]
        return {
            "sha": sha,
            "boundary": sha in graph.boundary_vertices,
            "subject": graph.records.get(sha, {}).get("subject"),
            "in_degree": incoming[i],
            "out_degree": outgoing[i],
            "degree": incoming[i] + outgoing[i],
            "incident_nonloop_edge_count": energies[i],
            "root_delta_D_norm_sq": energies[i],
            "vertex_delta_is_harmonic": energies[i] == 0,
        }

    roots = [vertex_description(i) for i, degree in enumerate(incoming) if degree == 0]
    terminals = [vertex_description(i) for i, degree in enumerate(outgoing) if degree == 0]
    selected_root = next((root for root in roots if not root["boundary"]), roots[0] if roots else None)
    if selected_root is not None:
        selected_root = {
            **selected_root,
            "derivation": "||D(delta_v,0)||^2 = ||B^T delta_v||^2 = (B B^T)[v,v]; a nonisolated root is not a zero mode",
        }
    first_cycle = cycle_descriptor(graph, cycles[0], 0) if cycles else None
    generated = datetime.now(timezone.utc).isoformat()
    if source_sha256 is None:
        source_sha256 = hashlib.sha256(
            json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        ).hexdigest()
        digest_kind = "canonical input JSON (no original file bytes supplied)"
    else:
        digest_kind = "original input file bytes"

    report = {
        "schema": REPORT_SCHEMA,
        "generated_at": generated,
        "source": {
            "path": source_path,
            "sha256": source_sha256,
            "digest_kind": digest_kind,
            "input_array": "commits",
            "display_compressed_nodes_used": False,
            "export_metadata": {
                key: data[key] for key in ("schema", "repository", "source", "window", "stats") if key in data
            },
        },
        "conventions": {
            "dataset": "observed Git parent graph; no declaration-DNA ancestry inferred",
            "complex": "unfilled graph 1-complex; no 2-cells",
            "edge_direction": "parent -> child",
            "parent_index": "zero-based position in the child's parents array",
            "incidence": "B has shape V x E; column e:u->v is -delta_u + delta_v",
            "cochain_differential": "d=B^T maps vertex values to oriented edge differences",
            "adjoint": "d*=B, with the standard unweighted Euclidean inner products",
            "Dirac": "D=[[0,B],[B^T,0]] on C^0 direct-sum C^1",
            "chirality": "Gamma=diag(+I_V,-I_E), cell-degree parity, not past/future",
            "index": "even-to-odd: dim ker(B^T) - dim ker(B) = n-m",
            "rank_method": "exact signed spanning-forest minor plus independent component indicators; no numerical rank estimation",
            "cycle_basis": "first-parent-preferred spanning forest; each nonforest edge is a +1 pivot",
            "coefficient_field": "integer certificates, interpreted over Q or R",
            "arithmetic": "sparse int64 with integer overflow bound checked",
            "directed_cycles": "allowed; acyclicity is not required for these identities",
            "boundary_policy": "missing parent identifiers become explicit vertices with unknown further ancestry",
            "root_and_tip_scope": "roots and tips of the complete supplied commits graph after boundary augmentation, not display compression or an assertion about unobserved history",
            "eigenvalues_computed": False,
            "lean_build_performed": False,
        },
        "metrics": {
            "vertices": n,
            "edges": m,
            "record_count": len(graph.records),
            "boundary_vertex_count": len(graph.boundary_vertices),
            "synthesized_boundary_vertex_count": len(graph.synthesized_boundary_vertices),
            "components": c,
            "rank_B": n - c,
            "betti0": c,
            "betti1": expected_b1,
            "dirac_dimension": n + m,
            "dirac_rank": 2 * (n - c),
            "dirac_kernel_dimension": c + expected_b1,
            "even_zero_modes": c,
            "odd_zero_modes": expected_b1,
            "chiral_index_even_to_odd": n - m,
            "euler_characteristic": n - m,
            "root_count": len(roots),
            "terminal_tip_count": len(terminals),
            "root_minus_tip_count": len(roots) - len(terminals),
            "merge_commits": sum(len(row["parents"]) > 1 for row in graph.records.values()),
            "extra_parent_edges": sum(max(0, len(row["parents"]) - 1) for row in graph.records.values()),
            "forest_edges": len(forest.edge_indices),
            "cycle_basis_vectors": len(cycles),
            "cycle_basis_nonzero_entries": int(Z.nnz),
            "self_loop_edges": sum(e.source == e.target for e in graph.edges),
            "incidence_nonzero_entries": int(B.nnz),
            "dirac_nonzero_entries": int(D.nnz),
            "commutator_nonzero_entries": int(commutator.nnz),
            "commutator_is_nonzero": commutator.nnz > 0,
            "trace_laplacian0": sum(energies),
        },
        "graph_structure": {
            "directed_acyclic": is_dag,
            "boundary_vertices": sorted(graph.boundary_vertices),
            "synthesized_boundary_vertices": sorted(graph.synthesized_boundary_vertices),
        },
        "checks": checks,
        "all_exact_checks_passed": all(checks.values()),
        "rank_derivation": {
            "lower_bound": "The forest minor deletes one row per weak component and pairs each nonroot vertex with its parent edge. Parent-before-child order makes it upper triangular with diagonal +/-1, so rank(B)>=n-c.",
            "upper_bound": "The c disjoint nonempty component-indicator vectors are independent and lie in ker(B^T), so rank(B)<=n-c.",
            "cycle_basis": "B Z=0 exactly. The nonforest-edge row submatrix of Z is the identity, so its m-n+c columns are independent and attain dim ker(B).",
            "Dirac_kernel": "ker(D)=ker(B^T) direct-sum ker(B), giving c+(m-n+c) zero modes; these are dimensions, not numerically computed eigenvalues.",
        },
        "roots": roots,
        "terminal_tips": terminals,
        "selected_root": selected_root,
        "representative_cycle": first_cycle,
        "witness": {
            "schema": WITNESS_SCHEMA,
            "cycle_count": len(cycles),
            "written": False,
            "path": None,
        },
    }
    return Analysis(graph, forest, cycles, B, D, Gamma, Z, report)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", required=True, type=Path, help="Full repository-evolution JSON export")
    parser.add_argument("--out", required=True, type=Path, help="Analysis JSON output")
    parser.add_argument("--witness-out", type=Path, help="Optional compact reconstructible cycle-basis JSON")
    args = parser.parse_args(argv)
    input_path = args.input.resolve()
    output_path = args.out.resolve()
    witness_path = args.witness_out.resolve() if args.witness_out else None
    if input_path == output_path or witness_path == input_path or witness_path == output_path:
        parser.error("Input, report, and witness paths must be distinct")
    raw = input_path.read_bytes()
    data = json.loads(raw)
    if not isinstance(data, dict):
        parser.error("Input JSON must be an object")
    analysis = analyze_export(
        data, source_path=str(input_path), source_sha256=hashlib.sha256(raw).hexdigest()
    )
    if witness_path is not None:
        witness_path.parent.mkdir(parents=True, exist_ok=True)
        witness_raw = (json.dumps(analysis.witness(), separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")
        witness_path.write_bytes(witness_raw)
        analysis.report["witness"].update({
            "written": True,
            "path": str(witness_path),
            "sha256": hashlib.sha256(witness_raw).hexdigest(),
            "bytes": len(witness_raw),
        })
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(analysis.report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"report": str(output_path), "metrics": analysis.report["metrics"], "all_exact_checks_passed": True}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
