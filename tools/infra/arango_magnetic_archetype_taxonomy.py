#!/usr/bin/env python3
"""Multi-Scale Magnetic / Spin-Glass Archetype Taxonomy Extractor for the InfoTree & Decl DAG.

Unifies five repository-native layers across renormalization scales (beta):
  1. Scale L_micro (beta -> inf): Expression DNA Fingerprints (typeFingerprint,
     valueFingerprint, shapeHash, de Bruijn depthHistogram) + directed WL hashes
     to extract exact/near-exact structural Alleles ("clone templates").
  2. Meso-Scale Couplings: `mcbal` Thermogravity / Spin-Glass Gibbs edge weights
     W_uv(beta) = m_uv * exp(-beta * E_uv) balanced by two-sided Sinkhorn Weyl
     gauge scaling P(beta) = diag(l) * W(beta) * diag(r).
  3. Directed Magnetic Laplacian (MagNet) & Flow Imbalance (DIGRAC):
     - Symmetric coupling: A_s(beta) = (P(beta) + P(beta)^T) / 2
     - Antisymmetric flow imbalance: F(beta) = P(beta) - P(beta)^T
     - Magnetic phase: Theta^{(q)}_uv = 2*pi*q * F_uv(beta) / (P_uv + P_vu + eps)
     - Hermitian Magnetic Laplacian: L^{(q,beta)} = D_s - A_s * exp(i * Theta^{(q)})
     - Spin-Glass Frustration / Hodge Curl Energy:
       E_frust(u -> v) = A_{s,uv} * |1 - exp(i * (theta_u - theta_v - Theta^{(q)}_uv))|^2
  4. Scale L_meso (beta = beta_meso): Spectral + DNA + Flow-Imbalance clustering into
     directed Code Species (`owner_source_species`, `bridge_intertwiner_species`,
     `frustrated_spinglass_corridor`, `algebraic_engine_species`, `capstone_sink_species`).
  5. Scale L_macro (beta = beta_macro): Coarse-grained Taxonomic Phyla with the
     DIGRAC Quotient Flow-Imbalance Matrix and Balaban Schur-complement effective
     coupling reduction.

Truth boundary:
  Derived navigation and taxonomy overlay only. Lean owner source and kernel
  verification remain the sole authority for mathematical truth.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy import sparse
from scipy.sparse import linalg as spla

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.arango_dag_algorithms import (
    REP_LAYERS,
    defect_cost,
    flow_polarity,
    layer_depth,
    process_boundary_class,
    process_defect_tags,
    process_dependency_role,
    run_aql,
)
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (
    ArangoTarget,
    CollectionSpec,
    collection_count,
    create_collection,
    drop_collection,
    ensure_database,
    list_collections,
)

SCHEMA = "info_geometry.magnetic_archetype_taxonomy.v1"
DECL_KINDS = ("def", "theorem", "structure", "inductive", "class", "instance", "axiom", "opaque")
DNA_FEATURE_NAMES = (
    "log_type_nodes",
    "log_val_nodes",
    "log_shape_nodes",
    "type_val_node_ratio",
    "type_app_ratio",
    "type_lam_ratio",
    "type_forall_ratio",
    "type_const_ratio",
    "val_app_ratio",
    "val_lam_ratio",
    "val_forall_ratio",
    "val_const_ratio",
    "val_redex_ratio",
    "debruijn_mean_depth",
    "debruijn_max_depth_log",
    "debruijn_entropy",
    "rep_depth_norm",
    "is_theorem_or_def_sign",
)


@dataclass(frozen=True)
class DeclGraphData:
    nodes: list[dict[str, Any]]
    node_index: dict[str, int]
    names: list[str]
    keys: list[str]
    modules: list[str]
    kinds: list[str]
    rep_layers: list[str | None]
    rep_depths: list[int | None]
    dag_shape_hashes: list[str]
    canonical_type_hashes: list[str]
    canonical_value_hashes: list[str]
    dna_matrix: np.ndarray  # shape (N, D)
    edges: list[tuple[int, int, str, int]]  # (src_idx, dst_idx, edge_kind, multiplicity)
    forward: list[list[int]]
    preds: list[list[int]]


def _extract_rep_depth_from_attrs(attrs: Any, explicit_layer: str | None = None, explicit_depth: int | None = None) -> tuple[str | None, int | None]:
    layer = explicit_layer
    depth = explicit_depth
    if isinstance(attrs, list):
        for item in attrs:
            text = str(item)
            if text.startswith("rep_layer:") and not layer:
                layer = text.split(":", 1)[1]
            elif text.startswith("rep_depth_nat:") and depth is None:
                try:
                    depth = int(text.split(":", 1)[1])
                except ValueError:
                    pass
    if depth is None and layer:
        depth = layer_depth(layer)
    return layer, depth


def _debruijn_stats(fp: dict[str, Any] | None) -> tuple[float, float, float]:
    if not isinstance(fp, dict):
        return 0.0, 0.0, 0.0
    hist = fp.get("depthHistogram")
    if not isinstance(hist, list) or not hist:
        return 0.0, 0.0, 0.0
    counts = [max(0, int(x)) for x in hist if isinstance(x, (int, float))]
    total = sum(counts)
    if total <= 0:
        return 0.0, 0.0, 0.0
    mean_d = sum(i * c for i, c in enumerate(counts)) / float(total)
    max_d = max((i for i, c in enumerate(counts) if c > 0), default=0)
    entropy = 0.0
    for c in counts:
        if c > 0:
            p = c / float(total)
            entropy -= p * math.log(p + 1e-15)
    return mean_d, math.log1p(max_d), entropy


def extract_decl_dna_vector(node: dict[str, Any], rep_depth: int | None) -> np.ndarray:
    """Extract an 18-dimensional structural DNA vector from compiler fingerprints."""
    decl_sub = node.get("decl") if isinstance(node.get("decl"), dict) else node
    tfp = decl_sub.get("typeFingerprint") if isinstance(decl_sub.get("typeFingerprint"), dict) else {}
    vfp = decl_sub.get("valueFingerprint") if isinstance(decl_sub.get("valueFingerprint"), dict) else {}
    sfp = decl_sub.get("shapeHash") if isinstance(decl_sub.get("shapeHash"), dict) else {}

    t_nodes = max(1, int(tfp.get("nodeCount") or 0))
    v_nodes = max(1, int(vfp.get("nodeCount") or 0))
    s_nodes = max(1, int(sfp.get("nodeCount") or 0))

    t_mean, t_max, t_ent = _debruijn_stats(tfp)
    v_mean, v_max, v_ent = _debruijn_stats(vfp)
    s_mean, s_max, s_ent = _debruijn_stats(sfp)

    mean_d = max(t_mean, v_mean, s_mean)
    max_d = max(t_max, v_max, s_max)
    ent_d = max(t_ent, v_ent, s_ent)

    kind = str(node.get("kind") or decl_sub.get("kind") or "unknown").lower()
    kind_sign = 1.0 if kind == "theorem" else (-1.0 if kind in {"def", "structure", "class", "inductive"} else 0.0)
    depth_norm = float(rep_depth) / 5.0 if rep_depth is not None else 0.5

    vec = np.array(
        [
            math.log1p(float(tfp.get("nodeCount") or 0)),
            math.log1p(float(vfp.get("nodeCount") or 0)),
            math.log1p(float(sfp.get("nodeCount") or 0)),
            float(t_nodes) / float(t_nodes + v_nodes),
            float(tfp.get("appCount") or 0) / float(t_nodes),
            float(tfp.get("lamCount") or 0) / float(t_nodes),
            float(tfp.get("forallCount") or 0) / float(t_nodes),
            float(tfp.get("constCount") or 0) / float(t_nodes),
            float(vfp.get("appCount") or 0) / float(v_nodes),
            float(vfp.get("lamCount") or 0) / float(v_nodes),
            float(vfp.get("forallCount") or 0) / float(v_nodes),
            float(vfp.get("constCount") or 0) / float(v_nodes),
            float(vfp.get("redexCount") or 0) / float(v_nodes),
            mean_d,
            max_d,
            ent_d,
            depth_norm,
            kind_sign,
        ],
        dtype=np.float64,
    )
    return vec


def _extract_hashes(node: dict[str, Any]) -> tuple[str, str, str]:
    decl_sub = node.get("decl") if isinstance(node.get("decl"), dict) else node
    dag_shape = str(node.get("dagShapeHash") or "")
    if not dag_shape and isinstance(decl_sub.get("shapeHash"), dict):
        dag_shape = str(decl_sub["shapeHash"].get("shapeHash") or "")
    elif not dag_shape and decl_sub.get("shapeHash"):
        dag_shape = str(decl_sub.get("shapeHash"))

    can_type = str(node.get("canonicalTypeHash") or "")
    if not can_type and isinstance(decl_sub.get("typeFingerprint"), dict):
        can_type = str(decl_sub["typeFingerprint"].get("shapeHash") or "")

    can_val = str(node.get("canonicalValueHash") or "")
    if not can_val and isinstance(decl_sub.get("valueFingerprint"), dict):
        can_val = str(decl_sub["valueFingerprint"].get("shapeHash") or "")

    return dag_shape or "unhashed_shape", can_type or "unhashed_type", can_val or "unhashed_val"


def build_decl_graph_from_rows(
    node_rows: list[dict[str, Any]],
    edge_rows: list[dict[str, Any]],
) -> DeclGraphData:
    """Construct a normalized DeclGraphData carrier from raw declaration and edge rows."""
    sorted_nodes = sorted(
        node_rows,
        key=lambda r: (str(r.get("name") or r.get("raw_name") or r.get("_key") or "")),
    )
    node_index: dict[str, int] = {}
    names: list[str] = []
    keys: list[str] = []
    modules: list[str] = []
    kinds: list[str] = []
    rep_layers: list[str | None] = []
    rep_depths: list[int | None] = []
    dag_shape_hashes: list[str] = []
    canonical_type_hashes: list[str] = []
    canonical_value_hashes: list[str] = []
    dna_rows: list[np.ndarray] = []

    for idx, row in enumerate(sorted_nodes):
        key = str(row.get("_key") or row.get("key") or f"node_{idx}")
        node_id = str(row.get("_id") or f"decls/{key}")
        name = str(row.get("name") or row.get("raw_name") or row.get("representative") or key)
        module = str(row.get("module") or (name.rsplit(".", 1)[0] if "." in name else ""))
        decl_sub = row.get("decl") if isinstance(row.get("decl"), dict) else row
        kind = str(row.get("kind") or decl_sub.get("kind") or "unknown")
        layer, depth = _extract_rep_depth_from_attrs(
            row.get("attrs") or decl_sub.get("attrs"),
            explicit_layer=row.get("rep_layer"),
            explicit_depth=row.get("rep_depth"),
        )
        sh_hash, ty_hash, val_hash = _extract_hashes(row)
        dna_vec = extract_decl_dna_vector(row, depth)

        node_index[node_id] = idx
        node_index[key] = idx
        node_index[name] = idx

        names.append(name)
        keys.append(key)
        modules.append(module)
        kinds.append(kind)
        rep_layers.append(layer)
        rep_depths.append(depth)
        dag_shape_hashes.append(sh_hash)
        canonical_type_hashes.append(ty_hash)
        canonical_value_hashes.append(val_hash)
        dna_rows.append(dna_vec)

    edge_accum: dict[tuple[int, int, str], int] = defaultdict(int)
    forward_sets: list[set[int]] = [set() for _ in sorted_nodes]
    pred_sets: list[set[int]] = [set() for _ in sorted_nodes]

    for erow in edge_rows:
        u = node_index.get(str(erow.get("_from") or ""))
        if u is None:
            u = node_index.get(str(erow.get("src") or ""))
        v = node_index.get(str(erow.get("_to") or ""))
        if v is None:
            v = node_index.get(str(erow.get("dst") or ""))
        if u is None or v is None or u == v:
            continue
        ekind = str(erow.get("kind") or "value")
        mult = max(1, int(erow.get("multiplicity") or 1))
        edge_accum[(u, v, ekind)] += mult
        forward_sets[u].add(v)
        pred_sets[v].add(u)

    edges = [(u, v, ekind, mult) for (u, v, ekind), mult in sorted(edge_accum.items())]
    forward = [sorted(s) for s in forward_sets]
    preds = [sorted(s) for s in pred_sets]

    # Infer topological depth stratum for nodes missing explicit rep_depth
    inferred_depths = list(rep_depths)
    if sorted_nodes:
        out_deg = [len(f) for f in forward]
        queue = [i for i, d in enumerate(out_deg) if d == 0]
        topo_level = [0] * len(sorted_nodes)
        rem_out = list(out_deg)
        head = 0
        while head < len(queue):
            curr = queue[head]
            head += 1
            for p in preds[curr]:
                if topo_level[p] < topo_level[curr] + 1:
                    topo_level[p] = topo_level[curr] + 1
                rem_out[p] -= 1
                if rem_out[p] == 0:
                    queue.append(p)
        max_lvl = max(topo_level, default=1) or 1
        for i in range(len(sorted_nodes)):
            if inferred_depths[i] is None:
                scaled = min(4, int(round(4.0 * topo_level[i] / float(max_lvl))))
                inferred_depths[i] = scaled
                dna_rows[i][16] = float(scaled) / 5.0

    dna_matrix = np.vstack(dna_rows) if dna_rows else np.zeros((0, len(DNA_FEATURE_NAMES)), dtype=np.float64)
    return DeclGraphData(
        nodes=sorted_nodes,
        node_index=node_index,
        names=names,
        keys=keys,
        modules=modules,
        kinds=kinds,
        rep_layers=rep_layers,
        rep_depths=inferred_depths,
        dag_shape_hashes=dag_shape_hashes,
        canonical_type_hashes=canonical_type_hashes,
        canonical_value_hashes=canonical_value_hashes,
        dna_matrix=dna_matrix,
        edges=edges,
        forward=forward,
        preds=preds,
    )


def load_arango_decl_graph(
    target: ArangoTarget,
    *,
    decls_collection: str = "decls",
    edges_collection: str = "edges",
    namespace_prefix: str = "InfoGeometry.Canonical",
    exclude_generated: bool = True,
    max_decls: int = 4000,
) -> DeclGraphData:
    """Load declarations and internal directed edges from live ArangoDB."""
    gen_filter = "FILTER d.generated != true" if exclude_generated else ""
    ns_filter = "FILTER STARTS_WITH(d.name, @ns_prefix)" if namespace_prefix else ""
    bind: dict[str, Any] = {
        "@decls": decls_collection,
        "limit": int(max_decls),
    }
    if namespace_prefix:
        bind["ns_prefix"] = namespace_prefix

    node_rows = run_aql(
        target,
        f"""
        FOR d IN @@decls
          {gen_filter}
          {ns_filter}
          SORT d.name ASC
          LIMIT @limit
          RETURN d
        """,
        bind,
    )
    if not node_rows:
        return build_decl_graph_from_rows([], [])

    ids = [str(r["_id"]) for r in node_rows if "_id" in r]
    edge_rows = run_aql(
        target,
        """
        FOR e IN @@edges
          FILTER e._from IN @ids AND e._to IN @ids
          RETURN {
            _key: e._key,
            _from: e._from,
            _to: e._to,
            src: e.src,
            dst: e.dst,
            kind: e.kind,
            multiplicity: 1
          }
        """,
        {"@edges": edges_collection, "ids": ids},
    )
    return build_decl_graph_from_rows(node_rows, edge_rows)


def compute_directed_wl_hashes(graph: DeclGraphData, rounds: int = 3) -> list[str]:
    """Compute directed Weisfeiler-Lehman hashes over (kind, dagShapeHash) + typed neighborhoods."""
    n = len(graph.nodes)
    if n == 0:
        return []
    out_by_kind: list[dict[str, list[int]]] = [{"type": [], "value": []} for _ in range(n)]
    in_by_kind: list[dict[str, list[int]]] = [{"type": [], "value": []} for _ in range(n)]
    for u, v, ekind, _ in graph.edges:
        slot = "type" if ekind == "type" else "value"
        out_by_kind[u][slot].append(v)
        in_by_kind[v][slot].append(u)

    colors = [
        hashlib.sha256(
            f"wl0:{graph.kinds[i]}:{graph.dag_shape_hashes[i]}".encode("utf-8")
        ).hexdigest()[:24]
        for i in range(n)
    ]
    for _ in range(max(0, rounds)):
        next_colors: list[str] = []
        for i in range(n):
            t_out = ",".join(sorted(colors[j] for j in out_by_kind[i]["type"]))
            v_out = ",".join(sorted(colors[j] for j in out_by_kind[i]["value"]))
            t_in = ",".join(sorted(colors[j] for j in in_by_kind[i]["type"]))
            v_in = ",".join(sorted(colors[j] for j in in_by_kind[i]["value"]))
            payload = f"{colors[i]}|to:{t_out}|vo:{v_out}|ti:{t_in}|vi:{v_in}"
            next_colors.append(hashlib.sha256(payload.encode("utf-8")).hexdigest()[:24])
        colors = next_colors
    return colors


def extract_micro_alleles(
    graph: DeclGraphData,
    wl_hashes: list[str],
    *,
    min_cluster_size: int = 2,
) -> list[dict[str, Any]]:
    """Scale L_micro (beta -> inf): Group declarations into structural Allele / Clone templates."""
    by_signature: dict[tuple[str, str, str], list[int]] = defaultdict(list)
    for i in range(len(graph.nodes)):
        sig = (graph.kinds[i], graph.dag_shape_hashes[i], wl_hashes[i])
        by_signature[sig].append(i)

    alleles: list[dict[str, Any]] = []
    for idx, ((kind, shape_hash, wl_hash), members) in enumerate(
        sorted(by_signature.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    ):
        if len(members) < min_cluster_size:
            continue
        modules = sorted({graph.modules[m] for m in members if graph.modules[m]})
        type_hashes = Counter(graph.canonical_type_hashes[m] for m in members)
        val_hashes = Counter(graph.canonical_value_hashes[m] for m in members)
        exact_type_clone = len(type_hashes) == 1 and "unhashed_type" not in type_hashes
        exact_val_clone = len(val_hashes) == 1 and "unhashed_val" not in val_hashes
        if exact_type_clone and exact_val_clone:
            allele_class = "exact_type_and_value_clone"
        elif exact_type_clone:
            allele_class = "exact_statement_template_clone"
        elif len(modules) > 1:
            allele_class = "cross_module_structural_homolog"
        else:
            allele_class = "intra_module_structural_motif"

        allele_key = hashlib.sha256(f"allele:{kind}:{shape_hash}:{wl_hash}".encode("utf-8")).hexdigest()[:24]
        alleles.append(
            {
                "_key": f"allele_{allele_key}",
                "allele_index": idx,
                "allele_class": allele_class,
                "decl_kind": kind,
                "dag_shape_hash": shape_hash,
                "wl_hash": wl_hash,
                "member_count": len(members),
                "distinct_module_count": len(modules),
                "modules": modules[:16],
                "representative": graph.names[members[0]],
                "sample_members": [graph.names[m] for m in members[:20]],
                "member_keys": [graph.keys[m] for m in members[:100]],
            }
        )
    return alleles


def compute_sinkhorn_gibbs_couplings(
    graph: DeclGraphData,
    *,
    beta: float = 2.0,
    sinkhorn_iterations: int = 15,
    defect_penalty_weight: float = 0.25,
) -> tuple[sparse.csr_matrix, list[dict[str, Any]]]:
    """Compute `mcbal` Thermogravity Gibbs couplings with two-sided Sinkhorn Weyl gauge scaling.

    Matches `InfoGeometry.LLM.McbalFullNativeCorridor`:
      1. Local interaction energy E_uv = d_cos(dna_u, dna_v) + gamma * defect_cost(u -> v)
      2. Gibbs kernel W_uv(beta) = mult_uv * exp(-beta * E_uv)
      3. Two-sided diagonal Weyl gauge scaling P(beta) = diag(l) * W(beta) * diag(r)
    """
    n = len(graph.nodes)
    if n == 0 or not graph.edges:
        return sparse.csr_matrix((n, n), dtype=np.float64), []

    norms = np.linalg.norm(graph.dna_matrix, axis=1, keepdims=True)
    norms = np.where(norms > 1e-12, norms, 1.0)
    unit_dna = graph.dna_matrix / norms

    pair_mult: dict[tuple[int, int], float] = defaultdict(float)
    pair_kinds: dict[tuple[int, int], set[str]] = defaultdict(set)
    for u, v, ekind, mult in graph.edges:
        weight = float(mult) * (1.25 if ekind == "value" else 1.0)
        pair_mult[(u, v)] += weight
        pair_kinds[(u, v)].add(ekind)

    rows: list[int] = []
    cols: list[int] = []
    vals: list[float] = []
    edge_meta: list[dict[str, Any]] = []

    for (u, v), mult_w in sorted(pair_mult.items()):
        cos_sim = float(np.clip(np.dot(unit_dna[u], unit_dna[v]), -1.0, 1.0))
        cos_dist = 0.5 * (1.0 - cos_sim)

        src_d = graph.rep_depths[u]
        dst_d = graph.rep_depths[v]
        src_cap = len(graph.preds[u]) == 0
        ekind = "type" if pair_kinds[(u, v)] == {"type"} else "value"
        role = process_dependency_role(src_d, dst_d, ekind)
        polarity = flow_polarity(src_d, dst_d)
        boundary = process_boundary_class(src_d, dst_d, role, src_cap)
        tags = process_defect_tags(
            src_depth=src_d,
            dst_depth=dst_d,
            src_capstone=src_cap,
            role=role,
            boundary=boundary,
            polarity=polarity,
            edge_kind=ekind,
        )
        d_cost = defect_cost(tags)
        energy = cos_dist + defect_penalty_weight * float(d_cost)
        boltzmann = mult_w * math.exp(-float(beta) * energy)

        rows.append(u)
        cols.append(v)
        vals.append(boltzmann)
        edge_meta.append(
            {
                "u": u,
                "v": v,
                "cosine_similarity": round(cos_sim, 6),
                "interaction_energy": round(energy, 6),
                "defect_cost": d_cost,
                "defect_tags": tags,
                "polarity": polarity,
                "boltzmann_weight": boltzmann,
            }
        )

    w_mat = sparse.csr_matrix((vals, (rows, cols)), shape=(n, n), dtype=np.float64)

    # Two-sided Sinkhorn diagonal Weyl gauge on the active row/column support
    left_scale = np.ones(n, dtype=np.float64)
    right_scale = np.ones(n, dtype=np.float64)
    w_csc = w_mat.tocsc()

    for _ in range(max(1, sinkhorn_iterations)):
        row_sums = np.asarray(w_mat.dot(right_scale)).reshape(-1)
        left_scale = np.divide(
            1.0,
            row_sums,
            out=np.ones_like(row_sums, dtype=np.float64),
            where=row_sums > 1e-12,
        )
        col_sums = np.asarray(w_csc.T.dot(left_scale)).reshape(-1)
        right_scale = np.divide(
            1.0,
            col_sums,
            out=np.ones_like(col_sums, dtype=np.float64),
            where=col_sums > 1e-12,
        )

    p_mat = sparse.diags(left_scale).dot(w_mat).dot(sparse.diags(right_scale)).tocsr()
    return p_mat, edge_meta


def compute_magnetic_laplacian_and_spectrum(
    p_mat: sparse.csr_matrix,
    *,
    q_charge: float = 0.25,
    n_eigen: int = 8,
) -> dict[str, Any]:
    """Build the Hermitian Magnetic Laplacian L^{(q,beta)} and extract its complex spectrum + frustration."""
    n = p_mat.shape[0]
    if n == 0:
        return {
            "eigenvalues": [],
            "eigenvectors": np.zeros((0, 0), dtype=np.complex128),
            "phases": np.zeros(0, dtype=np.float64),
            "node_frustration": np.zeros(0, dtype=np.float64),
            "flow_imbalance": np.zeros(0, dtype=np.float64),
            "hermitian_residual": 0.0,
            "total_frustration": 0.0,
        }

    p_t = p_mat.T.tocsr()
    a_sym = 0.5 * (p_mat + p_t)
    f_antisym = (p_mat - p_t).tocsr()

    out_flow = np.asarray(p_mat.sum(axis=1)).reshape(-1)
    in_flow = np.asarray(p_mat.sum(axis=0)).reshape(-1)
    total_flow = out_flow + in_flow
    flow_imbalance = np.divide(
        out_flow - in_flow,
        total_flow,
        out=np.zeros_like(total_flow, dtype=np.float64),
        where=total_flow > 1e-12,
    )

    coo_sym = a_sym.tocoo()
    if coo_sym.nnz == 0:
        return {
            "eigenvalues": [0.0],
            "eigenvectors": np.ones((n, 1), dtype=np.complex128) / math.sqrt(max(1, n)),
            "phases": np.zeros(n, dtype=np.float64),
            "node_frustration": np.zeros(n, dtype=np.float64),
            "flow_imbalance": flow_imbalance,
            "hermitian_residual": 0.0,
            "total_frustration": 0.0,
        }

    f_vals = np.asarray(f_antisym[coo_sym.row, coo_sym.col]).reshape(-1)
    s_vals = coo_sym.data
    net_ratio = np.divide(
        f_vals,
        2.0 * s_vals,
        out=np.zeros_like(s_vals, dtype=np.float64),
        where=s_vals > 1e-12,
    )
    theta_uv = 2.0 * math.pi * float(q_charge) * net_ratio
    mag_weights = s_vals * np.exp(1j * theta_uv)

    a_mag = sparse.csr_matrix(
        (mag_weights, (coo_sym.row, coo_sym.col)),
        shape=(n, n),
        dtype=np.complex128,
    )
    deg = np.asarray(a_sym.sum(axis=1)).reshape(-1)
    sqrt_deg = np.sqrt(np.maximum(deg, 0.0))
    inv_sqrt_deg = np.divide(
        1.0,
        sqrt_deg,
        out=np.zeros_like(sqrt_deg, dtype=np.float64),
        where=deg > 1e-12,
    )
    d_inv_sqrt = sparse.diags(inv_sqrt_deg.astype(np.complex128))
    ident = sparse.eye(n, dtype=np.complex128, format="csr")
    l_norm = (ident - d_inv_sqrt.dot(a_mag).dot(d_inv_sqrt)).tocsr()

    # Check exact Hermiticity ||L - L^H||_F
    diff = l_norm - l_norm.conj().T
    hermitian_residual = float(np.sqrt(np.sum(np.abs(diff.data) ** 2))) if diff.nnz else 0.0

    k = min(max(1, n_eigen), max(1, n - 2)) if n > 3 else max(1, n)
    if n <= 64:
        dense_l = l_norm.toarray()
        dense_l = 0.5 * (dense_l + dense_l.conj().T)
        evals, evecs = np.linalg.eigh(dense_l)
        evals = evals[:k]
        evecs = evecs[:, :k]
    else:
        try:
            evals, evecs = spla.eigsh(l_norm, k=k, which="SM", tol=1e-4, maxiter=2000)
            order = np.argsort(np.real(evals))
            evals = np.real(evals[order])
            evecs = evecs[:, order]
        except Exception:
            # Deterministic power-iteration fallback on D^{-1/2} A_mag D^{-1/2}
            norm_adj = d_inv_sqrt.dot(a_mag).dot(d_inv_sqrt)
            rng = np.random.default_rng(42)
            v0 = rng.standard_normal((n, k)) + 1j * rng.standard_normal((n, k))
            for _ in range(25):
                v0 = norm_adj.dot(v0)
                v0, _ = np.linalg.qr(v0)
            rayleigh = np.real(np.sum( np.conj(v0) * l_norm.dot(v0), axis=0 ))
            order = np.argsort(rayleigh)
            evals = rayleigh[order]
            evecs = v0[:, order]

    # Gauge-fix each eigenvector's global U(1) phase so the largest-magnitude entry is real positive
    for col_idx in range(evecs.shape[1]):
        col = evecs[:, col_idx]
        anchor = int(np.argmax(np.abs(col)))
        if np.abs(col[anchor]) > 1e-12:
            phase_fix = np.exp(-1j * np.angle(col[anchor]))
            evecs[:, col_idx] = col * phase_fix

    lead_mode = evecs[:, 1] if evecs.shape[1] > 1 and np.std(np.angle(evecs[:, 1])) > 1e-6 else evecs[:, 0]
    phases = np.angle(lead_mode)

    # Compute spin-glass frustration / Hodge curl defect per directed edge and per node
    phase_diff = phases[coo_sym.row] - phases[coo_sym.col] - theta_uv
    edge_frust = s_vals * (np.abs(1.0 - np.exp(1j * phase_diff)) ** 2)
    node_frust = np.zeros(n, dtype=np.float64)
    np.add.at(node_frust, coo_sym.row, 0.5 * edge_frust)
    np.add.at(node_frust, coo_sym.col, 0.5 * edge_frust)
    norm_node_frust = np.divide(
        node_frust,
        4.0 * deg,
        out=np.zeros_like(node_frust, dtype=np.float64),
        where=deg > 1e-12,
    )

    return {
        "eigenvalues": [round(float(x), 8) for x in np.real(evals)],
        "eigenvectors": evecs,
        "phases": phases,
        "node_frustration": norm_node_frust,
        "flow_imbalance": flow_imbalance,
        "hermitian_residual": hermitian_residual,
        "total_frustration": float(np.sum(edge_frust) * 0.5),
    }


def _deterministic_kmeans(features: np.ndarray, k: int, max_iter: int = 40) -> np.ndarray:
    """Deterministic farthest-first / k-means++ clustering without external sklearn dependency."""
    n = features.shape[0]
    if n == 0:
        return np.zeros(0, dtype=np.int64)
    k = max(1, min(k, n))
    if k == 1:
        return np.zeros(n, dtype=np.int64)

    norms = np.sum(features ** 2, axis=1)
    first = int(np.argmax(norms))
    centers = [features[first].copy()]
    min_sq_dist = np.sum((features - centers[0]) ** 2, axis=1)

    for _ in range(1, k):
        nxt = int(np.argmax(min_sq_dist))
        centers.append(features[nxt].copy())
        dist_new = np.sum((features - centers[-1]) ** 2, axis=1)
        min_sq_dist = np.minimum(min_sq_dist, dist_new)

    center_mat = np.vstack(centers)
    labels = np.zeros(n, dtype=np.int64)
    for _ in range(max_iter):
        dists = np.sum((features[:, None, :] - center_mat[None, :, :]) ** 2, axis=2)
        new_labels = np.argmin(dists, axis=1)
        if np.array_equal(new_labels, labels):
            break
        labels = new_labels
        for c_idx in range(k):
            mask = labels == c_idx
            if np.any(mask):
                center_mat[c_idx] = np.mean(features[mask], axis=0)
    return labels


def classify_species_role(
    *,
    mean_imbalance: float,
    mean_frustration: float,
    distinct_modules: int,
    member_count: int,
    out_flow_external: float,
    in_flow_external: float,
) -> str:
    """Assign a directed taxonomic archetype role from flow imbalance and magnetic frustration."""
    ext_total = out_flow_external + in_flow_external
    ext_imbalance = (out_flow_external - in_flow_external) / ext_total if ext_total > 1e-12 else mean_imbalance

    if mean_frustration >= 0.35 and out_flow_external > 1e-6 and in_flow_external > 1e-6:
        return "frustrated_spinglass_corridor"
    if ext_imbalance <= -0.35 or mean_imbalance <= -0.40:
        return "owner_source_species"
    if ext_imbalance >= 0.35 or mean_imbalance >= 0.40:
        return "capstone_sink_species"
    if distinct_modules >= 2 and out_flow_external > 1e-6 and in_flow_external > 1e-6:
        return "bridge_intertwiner_species"
    return "algebraic_engine_species"


def build_multiscale_taxonomy(
    graph: DeclGraphData,
    *,
    beta_meso: float = 2.0,
    beta_macro: float = 0.5,
    q_charge: float = 0.25,
    n_meso_clusters: int = 12,
    n_macro_phyla: int = 5,
    wl_rounds: int = 3,
    run_id: str = "live",
) -> dict[str, Any]:
    """Run the full 3-scale (Micro Allele -> Meso Magnetic Species -> Macro Phylum) extraction."""
    n = len(graph.nodes)
    wl_hashes = compute_directed_wl_hashes(graph, rounds=wl_rounds)
    alleles = extract_micro_alleles(graph, wl_hashes, min_cluster_size=2)

    p_meso, edge_meta = compute_sinkhorn_gibbs_couplings(graph, beta=beta_meso)
    mag_spec = compute_magnetic_laplacian_and_spectrum(
        p_meso,
        q_charge=q_charge,
        n_eigen=min(8, max(2, n_meso_clusters)),
    )

    evecs = mag_spec["eigenvectors"]
    phases = mag_spec["phases"]
    frust = mag_spec["node_frustration"]
    imbalance = mag_spec["flow_imbalance"]

    # Standardize DNA features for joint spectral-DNA embedding at scale beta_meso
    if n > 0:
        dna_mean = np.mean(graph.dna_matrix, axis=0, keepdims=True)
        dna_std = np.std(graph.dna_matrix, axis=0, keepdims=True)
        dna_std = np.where(dna_std > 1e-8, dna_std, 1.0)
        dna_z = (graph.dna_matrix - dna_mean) / dna_std

        spec_parts = [
            np.real(evecs),
            np.imag(evecs),
            np.cos(phases)[:, None],
            np.sin(phases)[:, None],
            imbalance[:, None] * 1.5,
            frust[:, None],
            math.sqrt(max(0.05, beta_meso)) * 0.35 * dna_z,
        ]
        joint_meso_features = np.hstack(spec_parts)
    else:
        joint_meso_features = np.zeros((0, 1), dtype=np.float64)

    k_meso = max(1, min(n_meso_clusters, max(1, n // 2 if n >= 6 else n)))
    meso_labels = _deterministic_kmeans(joint_meso_features, k=k_meso)

    # Compute cluster-to-cluster directed Sinkhorn flow matrix F_{C_a -> C_b}
    p_coo = p_meso.tocoo()
    cluster_flow = np.zeros((k_meso, k_meso), dtype=np.float64)
    for u, v, w in zip(p_coo.row, p_coo.col, p_coo.data):
        ca = int(meso_labels[u])
        cb = int(meso_labels[v])
        cluster_flow[ca, cb] += float(w)

    meso_species: list[dict[str, Any]] = []
    member_edges: list[dict[str, Any]] = []
    meso_centroids: list[np.ndarray] = []

    for c_idx in range(k_meso):
        members = [i for i in range(n) if int(meso_labels[i]) == c_idx]
        if not members:
            meso_centroids.append(np.zeros(joint_meso_features.shape[1], dtype=np.float64))
            continue

        out_ext = float(np.sum(cluster_flow[c_idx, :]) - cluster_flow[c_idx, c_idx])
        in_ext = float(np.sum(cluster_flow[:, c_idx]) - cluster_flow[c_idx, c_idx])
        internal_flow = float(cluster_flow[c_idx, c_idx])
        mean_imb = float(np.mean(imbalance[members]))
        mean_frust = float(np.mean(frust[members]))
        mean_phase = float(np.angle(np.mean(np.exp(1j * phases[members]))))

        mod_counts = Counter(graph.modules[m] for m in members if graph.modules[m])
        kind_counts = Counter(graph.kinds[m] for m in members)
        shape_counts = Counter(graph.dag_shape_hashes[m] for m in members)
        layer_counts = Counter(graph.rep_layers[m] for m in members if graph.rep_layers[m])
        dom_module = mod_counts.most_common(1)[0][0] if mod_counts else "unscoped"
        dom_layer = layer_counts.most_common(1)[0][0] if layer_counts else None

        role = classify_species_role(
            mean_imbalance=mean_imb,
            mean_frustration=mean_frust,
            distinct_modules=len(mod_counts),
            member_count=len(members),
            out_flow_external=out_ext,
            in_flow_external=in_ext,
        )

        # Rank members by closeness to cluster centroid
        sub_feats = joint_meso_features[members]
        centroid = np.mean(sub_feats, axis=0)
        meso_centroids.append(centroid)
        dists = np.linalg.norm(sub_feats - centroid[None, :], axis=1)
        ranked_members = [members[i] for i in np.argsort(dists)]

        species_key = f"species_{run_id}_{c_idx}_{role}"
        meso_species.append(
            {
                "_key": species_key,
                "schema": SCHEMA,
                "run_id": run_id,
                "scale": "L_meso",
                "beta": beta_meso,
                "q_charge": q_charge,
                "species_index": c_idx,
                "species_role": role,
                "dominant_module": dom_module,
                "dominant_rep_layer": dom_layer,
                "member_count": len(members),
                "distinct_module_count": len(mod_counts),
                "distinct_shape_hash_count": len(shape_counts),
                "decl_kind_histogram": dict(kind_counts),
                "mean_flow_imbalance": round(mean_imb, 6),
                "mean_magnetic_phase_rad": round(mean_phase, 6),
                "mean_spinglass_frustration": round(mean_frust, 6),
                "internal_sinkhorn_flow": round(internal_flow, 6),
                "external_out_flow": round(out_ext, 6),
                "external_in_flow": round(in_ext, 6),
                "centroid_representative": graph.names[ranked_members[0]],
                "sample_members": [graph.names[m] for m in ranked_members[:25]],
                "top_modules": [m for m, _ in mod_counts.most_common(8)],
                "labels": ["overlay:magnetic_archetype", f"role:{role}", "scale:L_meso"],
            }
        )
        for m in members:
            member_edges.append(
                {
                    "_key": f"sp_member_{run_id}_{c_idx}_{graph.keys[m]}"[:240],
                    "_from": f"decls/{graph.keys[m]}",
                    "_to": f"arango_dag_magnetic_archetypes/{species_key}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "decl_name": graph.names[m],
                    "species_index": c_idx,
                    "species_role": role,
                    "magnetic_phase_rad": round(float(phases[m]), 6),
                    "flow_imbalance": round(float(imbalance[m]), 6),
                    "spinglass_frustration": round(float(frust[m]), 6),
                    "wl_hash": wl_hashes[m],
                    "dag_shape_hash": graph.dag_shape_hashes[m],
                }
            )

    # Directed DIGRAC Flow-Imbalance Edges between Meso Species
    species_flow_edges: list[dict[str, Any]] = []
    for ca in range(k_meso):
        for cb in range(ca + 1, k_meso):
            f_ab = float(cluster_flow[ca, cb])
            f_ba = float(cluster_flow[cb, ca])
            tot = f_ab + f_ba
            if tot <= 1e-12:
                continue
            net = f_ab - f_ba
            src_c, dst_c = (ca, cb) if net >= 0 else (cb, ca)
            imb_ratio = abs(net) / tot
            species_flow_edges.append(
                {
                    "_key": f"sp_flow_{run_id}_{src_c}_to_{dst_c}",
                    "schema": SCHEMA,
                    "run_id": run_id,
                    "source_species": src_c,
                    "target_species": dst_c,
                    "forward_flow": round(max(f_ab, f_ba), 6),
                    "backward_flow": round(min(f_ab, f_ba), 6),
                    "net_flow": round(abs(net), 6),
                    "digrac_imbalance_ratio": round(imb_ratio, 6),
                    "regime": "directed_cascade" if imb_ratio >= 0.5 else "reciprocal_coupled",
                }
            )

    # Scale L_macro (beta = beta_macro): Coarse-grain Meso species into Macro Phyla
    # and compute the Balaban / Schur-complement effective precision reduction
    k_macro = max(1, min(n_macro_phyla, len(meso_species)))
    if meso_species:
        centroid_mat = np.vstack([meso_centroids[s["species_index"]] for s in meso_species])
        # Weight DNA dimensions by sqrt(beta_macro / beta_meso) to reflect higher-temperature coarse-graining
        macro_scale = math.sqrt(max(1e-3, beta_macro) / max(1e-3, beta_meso))
        centroid_mat[:, 6:] *= macro_scale
        phylum_assign = _deterministic_kmeans(centroid_mat, k=k_macro)
    else:
        phylum_assign = np.zeros(0, dtype=np.int64)

    macro_phyla: list[dict[str, Any]] = []
    for p_idx in range(k_macro):
        sp_indices = [
            meso_species[i]["species_index"]
            for i in range(len(meso_species))
            if int(phylum_assign[i]) == p_idx
        ]
        if not sp_indices:
            continue
        phylum_members = [i for i in range(n) if int(meso_labels[i]) in set(sp_indices)]
        roles = [
            s["species_role"]
            for s in meso_species
            if s["species_index"] in set(sp_indices)
        ]
        macro_phyla.append(
            {
                "phylum_index": p_idx,
                "scale": "L_macro",
                "beta": beta_macro,
                "species_indices": sp_indices,
                "total_declarations": len(phylum_members),
                "species_roles": dict(Counter(roles)),
                "mean_flow_imbalance": round(float(np.mean(imbalance[phylum_members])), 6) if phylum_members else 0.0,
                "mean_spinglass_frustration": round(float(np.mean(frust[phylum_members])), 6) if phylum_members else 0.0,
            }
        )

    # Balaban / Schur-Complement Coarse-Graining Diagnostic:
    # Partition nodes into Coarse Representatives C (1 centroid per Meso Species) and Fine Interior F
    schur_summary: dict[str, Any] = {"computed": False}
    if n >= 2 and meso_species:
        coarse_nodes = sorted(
            {
                graph.node_index[s["centroid_representative"]]
                for s in meso_species
                if s["centroid_representative"] in graph.node_index
            }
        )
        coarse_set = set(coarse_nodes)
        fine_nodes = [i for i in range(n) if i not in coarse_set]
        if coarse_nodes and fine_nodes:
            p_sym = 0.5 * (p_meso + p_meso.T)
            deg_s = np.asarray(p_sym.sum(axis=1)).reshape(-1)
            # Regularized positive-definite fine precision H = L_sym + reg * I (Balaban small-field operator)
            reg = 1e-2
            h_op = (sparse.diags(deg_s + reg) - p_sym).tocsr()
            h_cc = h_op[coarse_nodes, :][:, coarse_nodes].toarray()
            h_cf = h_op[coarse_nodes, :][:, fine_nodes]
            h_ff = h_op[fine_nodes, :][:, fine_nodes].tocsc()
            h_fc = h_cf.T.tocsc()
            try:
                solve_ff = spla.factorized(h_ff)
                eliminated = np.column_stack([solve_ff(h_fc[:, j].toarray().reshape(-1)) for j in range(len(coarse_nodes))])
                schur_s = h_cc - h_cf.dot(eliminated)
                schur_evals = np.linalg.eigvalsh(0.5 * (schur_s + schur_s.T))
                schur_summary = {
                    "computed": True,
                    "coarse_dimension": len(coarse_nodes),
                    "eliminated_fine_dimension": len(fine_nodes),
                    "schur_pos_def_verified": bool(np.all(schur_evals > 0)),
                    "min_schur_eigenvalue": round(float(np.min(schur_evals)), 8),
                    "max_schur_eigenvalue": round(float(np.max(schur_evals)), 8),
                    "trace_direct_coarse": round(float(np.trace(h_cc)), 6),
                    "trace_schur_effective": round(float(np.trace(schur_s)), 6),
                }
            except Exception as exc:
                schur_summary = {"computed": False, "reason": str(exc)}

    return {
        "schema": SCHEMA,
        "run_id": run_id,
        "truth_status": "derived_magnetic_taxonomy_not_lean_authority",
        "parameters": {
            "beta_meso": beta_meso,
            "beta_macro": beta_macro,
            "q_charge": q_charge,
            "wl_rounds": wl_rounds,
            "n_meso_clusters": k_meso,
            "n_macro_phyla": k_macro,
        },
        "graph_summary": {
            "declarations": n,
            "directed_edges": len(graph.edges),
            "distinct_modules": len(set(graph.modules)),
            "distinct_dag_shape_hashes": len(set(graph.dag_shape_hashes)),
            "distinct_wl_hashes": len(set(wl_hashes)),
        },
        "magnetic_laplacian_diagnostics": {
            "smallest_eigenvalues": mag_spec["eigenvalues"],
            "hermitian_residual_frobenius": round(mag_spec["hermitian_residual"], 14),
            "total_spinglass_frustration": round(mag_spec["total_frustration"], 6),
            "frustrated_ground_state": bool(
                mag_spec["eigenvalues"] and mag_spec["eigenvalues"][0] > 1e-5
            ),
        },
        "balaban_schur_coarse_graining": schur_summary,
        "scales": {
            "L_micro_alleles": {
                "allele_cluster_count": len(alleles),
                "top_alleles": alleles[:30],
            },
            "L_meso_species": {
                "species_count": len(meso_species),
                "role_distribution": dict(Counter(s["species_role"] for s in meso_species)),
                "species": meso_species,
                "digrac_species_flows": species_flow_edges,
            },
            "L_macro_phyla": {
                "phyla_count": len(macro_phyla),
                "phyla": macro_phyla,
            },
        },
        "_arango_rows": {
            "archetypes": meso_species,
            "member_edges": member_edges,
            "flow_edges": species_flow_edges,
        },
    }


def write_taxonomy_to_arango(
    target: ArangoTarget,
    taxonomy: dict[str, Any],
    *,
    drop_existing: bool = False,
    batch_size: int = 2000,
) -> dict[str, Any]:
    """Optionally persist derived magnetic archetype collections to ArangoDB."""
    from tools.infra.arango_dag_algorithms import import_batch

    specs = [
        CollectionSpec("arango_dag_magnetic_archetypes", False),
        CollectionSpec("arango_dag_magnetic_archetype_members", True),
        CollectionSpec("arango_dag_magnetic_archetype_flows", False),
    ]
    ensure_database(target)
    existing = list_collections(target)
    for spec in specs:
        if spec.name in existing and drop_existing:
            drop_collection(target, spec.name)
            existing.remove(spec.name)
        if spec.name not in existing:
            create_collection(target, spec)

    rows = taxonomy["_arango_rows"]
    return {
        "arango_dag_magnetic_archetypes": import_batch(
            target, "arango_dag_magnetic_archetypes", rows["archetypes"], batch_size=batch_size
        ),
        "arango_dag_magnetic_archetype_members": import_batch(
            target, "arango_dag_magnetic_archetype_members", rows["member_edges"], batch_size=batch_size
        ),
        "arango_dag_magnetic_archetype_flows": import_batch(
            target, "arango_dag_magnetic_archetype_flows", rows["flow_edges"], batch_size=batch_size
        ),
        "live_counts": {
            "arango_dag_magnetic_archetypes": collection_count(target, "arango_dag_magnetic_archetypes"),
            "arango_dag_magnetic_archetype_members": collection_count(target, "arango_dag_magnetic_archetype_members"),
            "arango_dag_magnetic_archetype_flows": collection_count(target, "arango_dag_magnetic_archetype_flows"),
        },
    }


def parse_args() -> argparse.Namespace:
    load_repo_arango_env()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-mode", choices=["arango", "jsonl"], default="arango")
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    parser.add_argument("--decls-collection", default="decls")
    parser.add_argument("--edges-collection", default="edges")
    parser.add_argument("--namespace-prefix", default="InfoGeometry.Canonical")
    parser.add_argument("--max-decls", type=int, default=3000)
    parser.add_argument("--nodes-jsonl", type=Path, default=None)
    parser.add_argument("--edges-jsonl", type=Path, default=None)
    parser.add_argument("--beta-meso", type=float, default=2.0)
    parser.add_argument("--beta-macro", type=float, default=0.5)
    parser.add_argument("--q-charge", type=float, default=0.25)
    parser.add_argument("--n-meso-clusters", type=int, default=12)
    parser.add_argument("--n-macro-phyla", type=int, default=5)
    parser.add_argument("--wl-rounds", type=int, default=3)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path("artifacts/dag/magnetic_archetype_taxonomy_report.json"),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    run_id = str(int(time.time()))
    t0 = time.perf_counter()

    if args.source_mode == "jsonl":
        if not args.nodes_jsonl or not args.edges_jsonl:
            raise ValueError("--nodes-jsonl and --edges-jsonl are required when --source-mode=jsonl")
        node_rows = [
            json.loads(line)
            for line in args.nodes_jsonl.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        edge_rows = [
            json.loads(line)
            for line in args.edges_jsonl.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        graph = build_decl_graph_from_rows(node_rows[: args.max_decls], edge_rows)
        target = None
    else:
        target = ArangoTarget(
            endpoint=str(args.endpoint).rstrip("/"),
            database=str(args.database),
            username=str(args.username),
            password=str(args.password),
        )
        graph = load_arango_decl_graph(
            target,
            decls_collection=str(args.decls_collection),
            edges_collection=str(args.edges_collection),
            namespace_prefix=str(args.namespace_prefix),
            max_decls=int(args.max_decls),
        )

    load_seconds = time.perf_counter() - t0
    t1 = time.perf_counter()
    taxonomy = build_multiscale_taxonomy(
        graph,
        beta_meso=float(args.beta_meso),
        beta_macro=float(args.beta_macro),
        q_charge=float(args.q_charge),
        n_meso_clusters=int(args.n_meso_clusters),
        n_macro_phyla=int(args.n_macro_phyla),
        wl_rounds=int(args.wl_rounds),
        run_id=run_id,
    )
    compute_seconds = time.perf_counter() - t1

    write_report = None
    if args.write and target is not None:
        write_report = write_taxonomy_to_arango(
            target,
            taxonomy,
            drop_existing=bool(args.drop_existing),
        )

    # Strip bulk _arango_rows from JSON report file to keep report compact & readable
    report = {k: v for k, v in taxonomy.items() if k != "_arango_rows"}
    report["timing"] = {
        "load_seconds": round(load_seconds, 3),
        "compute_seconds": round(compute_seconds, 3),
    }
    report["write"] = write_report

    out_path = args.json_out.resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")

    gs = report["graph_summary"]
    diag = report["magnetic_laplacian_diagnostics"]
    meso = report["scales"]["L_meso_species"]
    micro = report["scales"]["L_micro_alleles"]
    print(f"Magnetic archetype taxonomy report written: {out_path}")
    print(
        f"Loaded decls={gs['declarations']} directed_edges={gs['directed_edges']} "
        f"modules={gs['distinct_modules']} shape_hashes={gs['distinct_dag_shape_hashes']}"
    )
    print(
        f"Micro alleles={micro['allele_cluster_count']} | "
        f"Meso species={meso['species_count']} roles={json.dumps(meso['role_distribution'])} | "
        f"Hermitian_res={diag['hermitian_residual_frobenius']} total_frust={diag['total_spinglass_frustration']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
