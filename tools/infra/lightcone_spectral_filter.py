#!/usr/bin/env python3
"""Local Schur/Drazin/Hodge diagnostics for bounded causal lightcones.

This script intentionally works on *bounded local slices* such as lean-graph
projections or causal cone prompt packets.  It must not be used as a dense
operator over the full Mathlib/repository DAG.

Authority boundary:
  - output is a numerical/navigation diagnostic;
  - Lean remains proof authority;
  - Arango/hydrated DAG artifacts remain derived navigation layers.

Supported inputs:
  1. lean-graph rows:
       [{"name": "A", "references": ["B", ...]}, ...]
     where `references = dependencies`.

  2. causal cone prompt packets from arango_causal_chiral_cone_prompt.py.
     The parser is deliberately tolerant and extracts component/name rows from
     apex/backward/forward cone fields when present.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

try:
    import numpy as np
    from scipy import linalg as la
except ModuleNotFoundError:
    np = None
    la = None

SCHEMA = "info_geometry.local_lightcone_spectral_filter.v1"
DEFAULT_OUT = Path("reports/dag/local-lightcone-spectral-filter.json")


def require_numeric_stack() -> None:
    if np is None or la is None:
        raise SystemExit(
            "lightcone_spectral_filter requires numpy and scipy. "
            "Run via `.venv-py312/bin/python` or install the project numeric stack."
        )


def stable_node_name(row: dict[str, Any], fallback: str) -> str:
    for key in ("name", "representative", "componentId", "id", "_key"):
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return fallback


def _iter_nested_dicts(value: Any) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    if isinstance(value, dict):
        out.append(value)
        for child in value.values():
            out.extend(_iter_nested_dicts(child))
    elif isinstance(value, list):
        for child in value:
            out.extend(_iter_nested_dicts(child))
    return out


def load_rows_and_edges(path: Path) -> tuple[list[str], list[tuple[str, str]], str]:
    """Return node names and causal-flow edges `dependency -> user`.

    lean-graph rows store `node.references = dependencies`, i.e. node -> dep.
    For local proof/information flow we invert those references to dep -> node.
    """
    payload = json.loads(path.read_text(encoding="utf-8"))

    if isinstance(payload, list):
        names: list[str] = []
        rows_by_name: dict[str, dict[str, Any]] = {}
        for i, row in enumerate(payload):
            if not isinstance(row, dict):
                continue
            name = stable_node_name(row, f"node:{i}")
            if name in rows_by_name:
                raise SystemExit(f"duplicate node name in input slice: {name}")
            names.append(name)
            rows_by_name[name] = row
        name_set = set(names)
        edges: list[tuple[str, str]] = []
        for user, row in rows_by_name.items():
            for ref in row.get("references") or []:
                if isinstance(ref, str) and ref in name_set and ref != user:
                    edges.append((ref, user))
        return names, sorted(set(edges)), "lean_graph_references_dependencies"

    if not isinstance(payload, dict):
        raise SystemExit(f"unsupported JSON shape in {path}: expected object or list")

    nodes: dict[str, dict[str, Any]] = {}
    edges: set[tuple[str, str]] = set()

    def add_node(row: dict[str, Any]) -> str:
        name = stable_node_name(row, f"node:{len(nodes)}")
        nodes.setdefault(name, row)
        return name

    for key in ("apex", "apex_proposition"):
        row = payload.get(key)
        if isinstance(row, dict):
            add_node(row)

    for field in ("backward_cone", "forward_cone", "members", "source_excerpts"):
        for row in payload.get(field) or []:
            if isinstance(row, dict):
                for nested in _iter_nested_dicts(row):
                    if any(k in nested for k in ("name", "representative", "componentId", "id", "_key")):
                        add_node(nested)

    # Prefer explicit edge-like rows if present.
    for row in _iter_nested_dicts(payload):
        src = row.get("source") or row.get("from") or row.get("dependency") or row.get("dep")
        dst = row.get("target") or row.get("to") or row.get("user") or row.get("dependent")
        if isinstance(src, str) and isinstance(dst, str):
            nodes.setdefault(src, {"name": src})
            nodes.setdefault(dst, {"name": dst})
            edges.add((src, dst))

    names = sorted(nodes)
    return names, sorted(edges), "causal_cone_packet_tolerant"


def adjacency_matrix(names: list[str], edges: list[tuple[str, str]]) -> np.ndarray:
    require_numeric_stack()
    idx = {name: i for i, name in enumerate(names)}
    a = np.zeros((len(names), len(names)), dtype=float)
    for src, dst in edges:
        i = idx.get(src)
        j = idx.get(dst)
        if i is not None and j is not None and i != j:
            a[i, j] = 1.0
    return a


def matrix_norm(x: np.ndarray) -> float:
    require_numeric_stack()
    return float(la.norm(x, ord="fro"))


def estimate_nilpotent_index(n_block: np.ndarray, tol: float) -> int:
    if n_block.size == 0:
        return 0
    power = np.array(n_block, copy=True)
    for k in range(1, n_block.shape[0] + 2):
        if matrix_norm(power) <= tol:
            return k
        power = power @ n_block
    return n_block.shape[0] + 1


def compute_drazin_from_schur(a: np.ndarray, tol: float = 1e-9) -> dict[str, Any]:
    """Compute a numerical Drazin inverse using ordered complex Schur form.

    The Schur form is ordered with nonzero eigenvalues first.  For

        T = [[C, D], [0, N]]

    with C invertible and N the zero-spectrum block, the Drazin inverse in this
    basis is

        T^D = [[C^-1, X], [0, 0]]

    where X solves the Sylvester equation C X - X N = C^-1 D.  This off-diagonal
    term is the important correction missing from the naive block inverse.
    """
    require_numeric_stack()
    n = a.shape[0]
    if n == 0:
        z = np.zeros((0, 0), dtype=float)
        return {"drazin": z, "projector": z, "index": 0, "nonzero_dim": 0, "residuals": {}}

    def select_nonzero(x: complex) -> bool:
        return abs(x) > tol

    t, z, nonzero_dim = la.schur(a.astype(complex), output="complex", sort=select_nonzero)
    m = int(nonzero_dim)
    td = np.zeros_like(t, dtype=complex)

    if m > 0:
        c = t[:m, :m]
        c_inv = la.inv(c)
        td[:m, :m] = c_inv
        if m < n:
            d = t[:m, m:]
            n_block = t[m:, m:]
            rhs = c_inv @ d
            td[:m, m:] = la.solve_sylvester(c, -n_block, rhs)
    n_block = t[m:, m:] if m < n else np.zeros((0, 0), dtype=complex)
    index = estimate_nilpotent_index(n_block, tol)

    z_inv = z.conj().T
    drazin = z @ td @ z_inv
    drazin = np.real_if_close(drazin, tol=1000)
    if np.iscomplexobj(drazin):
        drazin = drazin.real
    projector = np.real_if_close(a @ drazin, tol=1000)
    if np.iscomplexobj(projector):
        projector = projector.real

    ak = np.linalg.matrix_power(a, max(index, 0))
    ak1 = ak @ a
    residuals = {
        "commutator_frobenius": matrix_norm(a @ drazin - drazin @ a),
        "drazin_power_frobenius": matrix_norm(ak1 @ drazin - ak),
        "reflexive_frobenius": matrix_norm(drazin @ a @ drazin - drazin),
        "projector_idempotent_frobenius": matrix_norm(projector @ projector - projector),
    }
    return {
        "drazin": np.asarray(drazin, dtype=float),
        "projector": np.asarray(projector, dtype=float),
        "index": int(index),
        "nonzero_dim": m,
        "residuals": residuals,
    }


def local_hodge_core(a: np.ndarray, tol: float) -> dict[str, Any]:
    """Compute a symmetric local graph Laplacian and its harmonic basis."""
    require_numeric_stack()
    if a.shape[0] == 0:
        return {"eigenvalues": [], "harmonic_dim": 0, "harmonic_weights": []}
    undirected = np.maximum(a, a.T)
    degree = np.diag(np.sum(undirected, axis=1))
    lap = degree - undirected
    vals, vecs = la.eigh(lap)
    mask = np.abs(vals) <= tol
    harmonic = vecs[:, mask]
    weights = np.sum(harmonic * harmonic, axis=1) if harmonic.size else np.zeros(a.shape[0])
    return {
        "eigenvalues": [float(x) for x in vals.tolist()],
        "harmonic_dim": int(np.count_nonzero(mask)),
        "harmonic_weights": [float(x) for x in weights.tolist()],
    }


def node_scores(names: list[str], a: np.ndarray, projector: np.ndarray, harmonic_weights: list[float]) -> list[dict[str, Any]]:
    require_numeric_stack()
    ident_minus_p = np.eye(len(names)) - projector if len(names) else projector
    out_degree = np.sum(a, axis=1) if len(names) else []
    in_degree = np.sum(a, axis=0) if len(names) else []
    rows: list[dict[str, Any]] = []
    for i, name in enumerate(names):
        core_weight = float(la.norm(projector[i, :]) + la.norm(projector[:, i]))
        nil_weight = float(la.norm(ident_minus_p[i, :]) + la.norm(ident_minus_p[:, i]))
        rows.append(
            {
                "name": name,
                "in_degree": int(in_degree[i]),
                "out_degree": int(out_degree[i]),
                "drazin_core_weight": core_weight,
                "nilpotent_residue_weight": nil_weight,
                "hodge_harmonic_weight": float(harmonic_weights[i]) if i < len(harmonic_weights) else 0.0,
            }
        )
    rows.sort(key=lambda r: (-(r["drazin_core_weight"] + r["hodge_harmonic_weight"]), r["name"]))
    return rows


def finite_or_none(value: float) -> float | None:
    return value if math.isfinite(value) else None


def build_report(path: Path, *, tol: float, max_nodes: int) -> dict[str, Any]:
    names, edges, input_mode = load_rows_and_edges(path)
    if len(names) > max_nodes:
        raise SystemExit(
            f"refusing dense local spectral filter on {len(names)} nodes; "
            f"raise --max-nodes explicitly if this is still a bounded lightcone"
        )
    a = adjacency_matrix(names, edges)
    drazin = compute_drazin_from_schur(a, tol=tol)
    hodge = local_hodge_core(a, tol=tol)
    scores = node_scores(names, a, drazin["projector"], hodge["harmonic_weights"])
    edge_density = (len(edges) / (len(names) * (len(names) - 1))) if len(names) > 1 else 0.0
    return {
        "schema": SCHEMA,
        "input": str(path),
        "input_mode": input_mode,
        "orientation": "local matrix edges are dependency -> user causal-flow edges",
        "node_count": len(names),
        "edge_count": len(edges),
        "edge_density": finite_or_none(float(edge_density)),
        "tolerance": tol,
        "drazin": {
            "index": drazin["index"],
            "nonzero_schur_dim": drazin["nonzero_dim"],
            "residuals": drazin["residuals"],
            "projector_trace": finite_or_none(float(np.trace(drazin["projector"]))),
        },
        "hodge": {
            "harmonic_dim": hodge["harmonic_dim"],
            "smallest_eigenvalues": hodge["eigenvalues"][: min(12, len(hodge["eigenvalues"]))],
        },
        "nodes": scores,
        "warning": (
            "Numerical local-lightcone diagnostic only.  This is not a Lean proof, "
            "not a global Mathlib operator, and not a replacement for Arango/Lean witnesses."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Bounded lean-graph slice or causal cone packet JSON")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--tol", type=float, default=1e-9)
    parser.add_argument("--max-nodes", type=int, default=500)
    args = parser.parse_args()

    report = build_report(args.input, tol=args.tol, max_nodes=args.max_nodes)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"wrote local lightcone spectral report to {args.json_out}")
    print(f"nodes={report['node_count']} edges={report['edge_count']} harmonic_dim={report['hodge']['harmonic_dim']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
