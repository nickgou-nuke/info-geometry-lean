#!/usr/bin/env python3
"""
Build conservative chiral patches over the declaration graph.
Implements the v1.1 specification for Level 2 spectral navigation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

import networkx as nx
import numpy as np
from scipy.sparse.linalg import eigsh

# --- Schema and Policy ---
RUN_SCHEMA_VERSION = "ig.patch_run.v1"
PATCH_SCHEMA_VERSION = "ig.chiral_patch.v1.2"
MEMBER_SCHEMA_VERSION = "ig.patch_member.v1"
EDGE_SCHEMA_VERSION = "ig.patch_edge.v1"
SPECTRAL_SCHEMA_VERSION = "ig.patch_spectral_signature.v1.2"
ALGORITHM_VERSION = "chiral_patch_hashes.v1.2"
NODE_COLLECTION = "ig_nodes"
PATCH_COLLECTION = "ig_chiral_patches"

# --- Data Structures ---

@dataclass
class PatchRun:
    _key: str
    schema_version: str
    source_graph_hash: str
    expr_fingerprint_version: str
    patch_algorithm: str
    created_at: str
    patch_run_id: str = ""
    run_id: str = ""
    algorithm_version: str = ALGORITHM_VERSION
    fingerprints_available: bool = False
    authority_level: str = "derived"
    claim_scope: str = "derived_spectral_neighborhood_sidecar"
    non_overclaim: bool = True

@dataclass
class ChiralPatch:
    _key: str
    patch_id: str
    patch_type: str
    run_id: str
    node_count: int
    edge_count: int
    coarse_hash: str
    debruijn_histogram: list[int]
    chiral_entropy: float
    chiral_bias: float
    cartan_proxy_histogram: dict[str, int]
    level: int = 2
    schema_version: str = PATCH_SCHEMA_VERSION
    patch_run_id: str = ""
    algorithm_version: str = ALGORITHM_VERSION
    claim_scope: str = "derived_spectral_neighborhood_sidecar"
    non_overclaim: bool = True
    authority_level: str = "derived"
    cartan_proxy_sector: str = "unknown"
    cartan_proxy_policy: str = "annotation_only_no_cartan_decomposition_claim"
    redex_density: float = 0.0
    max_debruijn_depth: int = 0

@dataclass
class PatchMember:
    _from: str
    _to: str
    membership_type: str
    local_role: str = "member"
    schema_version: str = MEMBER_SCHEMA_VERSION
    patch_run_id: str = ""
    patch_id: str = ""
    membership_weight: float = 1.0

@dataclass
class PatchEdge:
    _from: str
    _to: str
    edge_type: str = "PATCH_DEPENDS_ON"
    action_weight: float = 1.0
    affinity: float = 0.0
    cartan_proxy_sector: str = "unknown"
    schema_version: str = EDGE_SCHEMA_VERSION
    patch_run_id: str = ""
    from_patch_id: str = ""
    to_patch_id: str = ""
    transport_count: int = 1

@dataclass
class SpectralSignature:
    _key: str
    patch_id: str
    eigenvalues: list[float]
    nullity: int
    pseudo_logdet: float
    schema_version: str = SPECTRAL_SCHEMA_VERSION
    patch_run_id: str = ""
    run_id: str = ""
    laplacian: str = "sym_normalized_v1"
    spectral_status: str = "exact"
    authority_level: str = "derived"
    claim_scope: str = "derived_spectral_neighborhood_sidecar"
    non_overclaim: bool = True

# --- Core Logic ---

def stable_key(raw: str) -> str:
    """Return an Arango-safe deterministic key."""
    cleaned = re.sub(r"[^A-Za-z0-9_.:-]+", "_", raw)
    if len(cleaned) <= 180:
        return cleaned
    digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]
    return f"{cleaned[:150]}_{digest}"


def doc_id(collection: str, key_or_id: str) -> str:
    if "/" in key_or_id:
        return key_or_id
    return f"{collection}/{key_or_id}"


def patch_doc_id(patch_id: str) -> str:
    return doc_id(PATCH_COLLECTION, patch_id)


def normalize_node_key(raw: Any) -> str:
    value = str(raw or "").strip()
    if not value:
        return ""
    if "/" in value:
        return value
    return doc_id(NODE_COLLECTION, value)


def hash_input_files(paths: Iterable[Path | None]) -> str:
    h = hashlib.sha256()
    for path in paths:
        if path is None:
            h.update(b"<missing>")
            continue
        h.update(str(path).encode("utf-8"))
        h.update(b"\0")
        h.update(path.read_bytes())
        h.update(b"\0")
    return "sha256:" + h.hexdigest()


def compute_spectral_signature(
    G: nx.Graph,
    k: int = 10,
    max_exact_nodes: int = 750,
) -> tuple[list[float], int, float, str]:
    if G.number_of_nodes() < 2:
        return [], 0, 0.0, "trivial"
    
    try:
        if G.number_of_nodes() <= max_exact_nodes:
            L = nx.normalized_laplacian_matrix(G).toarray()
            evals = np.linalg.eigvalsh(L)
            status = "exact"
        else:
            L = nx.normalized_laplacian_matrix(G).astype(float)
            approx_k = min(max(k + nx.number_connected_components(G) + 2, 2), G.number_of_nodes() - 1)
            evals = eigsh(L, k=approx_k, which="SM", return_eigenvectors=False)
            status = "truncated"
        evals = np.sort(evals)
        
        # Nullity (count eigenvalues near zero)
        nullity = int(np.sum(evals < 1e-10))
        
        # Non-zero eigenvalues for logdet
        nonzero = evals[evals > 1e-10]
        pseudo_logdet = float(np.sum(np.log(nonzero))) if nonzero.size > 0 else 0.0
        
        # Top k nonzero eigenvalues (bucketed/truncated)
        signature_vals = [round(float(v), 4) for v in nonzero[:k]]
        
        return signature_vals, nullity, pseudo_logdet, status
    except Exception:
        return [], 0, 0.0, "failed"

def cartan_proxy_sector(edge_data: dict[str, Any]) -> str:
    explicit = str(edge_data.get("cartan_proxy_sector", "") or "")
    if explicit in {"k_even", "p_odd", "mixed", "unknown"}:
        return explicit
    kind = str(edge_data.get("kind", edge_data.get("edgeKind", "")) or "")
    if kind in {
        "same_shape",
        "rename",
        "defeq",
        "definitional_equivalence",
        "verified_equivalence",
        "import_preserving_refactor",
    }:
        return "k_even"
    if kind in {
        "proposed_beta_reduction",
        "beta_reduction",
        "apply_new_lemma",
        "expansion",
        "proof_transformation",
        "shape_hash_change",
    }:
        return "p_odd"
    orientation = str(edge_data.get("chiral_orientation", edge_data.get("time_direction", "")) or "")
    if orientation == "mixed":
        return "mixed"
    return "unknown"


def dominant_cartan_sector(histogram: dict[str, int], threshold: float = 0.65) -> str:
    total = sum(histogram.values())
    if total == 0:
        return "unknown"
    sector, count = max(histogram.items(), key=lambda item: (item[1], item[0]))
    return sector if count / total >= threshold else "mixed"


def compute_chiral_metrics(sub_G: nx.DiGraph) -> tuple[float, float, dict[str, int]]:
    forward = 0
    backward = 0
    mixed = 0
    
    cartan_counts = Counter()
    
    for u, v, d in sub_G.edges(data=True):
        direction = d.get("chiral_orientation", d.get("time_direction", "forward"))
        if direction == "forward":
            forward += 1
        elif direction == "backward":
            backward += 1
        else:
            mixed += 1
            
        sector = cartan_proxy_sector(d)
        cartan_counts[sector] += 1
        
    total = forward + backward + mixed
    if total == 0:
        return 0.0, 0.0, {}
        
    p_f = forward / total
    p_b = backward / total
    p_m = mixed / total
    
    # Chiral entropy
    probs = [p for p in [p_f, p_b, p_m] if p > 0]
    entropy = -sum(p * np.log2(p) for p in probs)
    
    # Chiral bias
    bias = (forward - backward) / total
    
    for sector in ("k_even", "p_odd", "mixed", "unknown"):
        cartan_counts.setdefault(sector, 0)
    return float(entropy), float(bias), dict(cartan_counts)


def fingerprint_bucket(row: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    counts = row.get("feature_counts", {}) if isinstance(row.get("feature_counts"), dict) else {}
    shape = str(row.get("level_1_local_hash", row.get("shapeHash", row.get("shape_hash", ""))) or "")
    binder = row.get("binder_bucket", row.get("binderPattern", counts.get("binder_depth_proxy", "unknown")))
    token = row.get("token_bucket", row.get("tokenPattern", counts.get("token_count", "unknown")))
    redex = row.get("redex_bucket", row.get("redexPattern", counts.get("redex_proxy", "unknown")))
    root = str(row.get("exprTag", row.get("rootTag", shape or "unknown")) or "unknown")
    if shape:
        bucket = f"shape={shape}"
    else:
        bucket = f"binder={binder}|token={token}|redex={redex}|root={root}"
    return bucket, {
        "shape_hash": shape or None,
        "binder_bucket": binder,
        "token_bucket": token,
        "redex_bucket": redex,
        "root_tag": root,
    }


def fingerprint_features(node_ids: Iterable[str], fingerprints: dict[str, dict]) -> tuple[list[int], float, int]:
    hist = np.zeros(10, dtype=int)
    redex_total = 0.0
    token_total = 0.0
    max_depth = 0
    for node_id in node_ids:
        f = fingerprints.get(node_id, {})
        h = f.get("depthHistogram", f.get("debruijn_histogram", []))
        if isinstance(h, list):
            for j, val in enumerate(h[:10]):
                hist[j] += int(val)
        counts = f.get("feature_counts", {}) if isinstance(f.get("feature_counts"), dict) else {}
        max_depth = max(max_depth, int(counts.get("binder_depth_proxy", f.get("max_debruijn_depth", 0)) or 0))
        redex_total += float(counts.get("redex_proxy", f.get("redex_count", 0)) or 0)
        token_total += max(float(counts.get("token_count", f.get("token_count", 0)) or 0), 0.0)
    redex_density = redex_total / token_total if token_total else 0.0
    return hist.tolist(), float(round(redex_density, 6)), max_depth


def build_patch_dependency_edges(
    edges: list[dict],
    patch_membership: dict[str, set[str]],
    run_id: str,
) -> list[PatchEdge]:
    node_to_patches: dict[str, set[str]] = defaultdict(set)
    patch_sizes = {patch_id: max(1, len(nodes)) for patch_id, nodes in patch_membership.items()}
    for patch_id, nodes in patch_membership.items():
        for node_id in nodes:
            node_to_patches[node_id].add(patch_id)

    edge_counts: Counter[tuple[str, str]] = Counter()
    sector_counts: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    weight_counts: Counter[tuple[str, str]] = Counter()

    for edge in edges:
        src = edge.get("_from")
        dst = edge.get("_to")
        if not isinstance(src, str) or not isinstance(dst, str):
            continue
        for from_patch in node_to_patches.get(src, set()):
            for to_patch in node_to_patches.get(dst, set()):
                if from_patch == to_patch:
                    continue
                key = (from_patch, to_patch)
                edge_counts[key] += 1
                weight_counts[key] += float(edge.get("action_weight", edge.get("weight", 1.0)) or 1.0)
                sector_counts[key][cartan_proxy_sector(edge)] += 1

    patch_edges: list[PatchEdge] = []
    for (from_patch, to_patch), count in sorted(edge_counts.items()):
        denom = (patch_sizes[from_patch] * patch_sizes[to_patch]) ** 0.5
        sector = sector_counts[(from_patch, to_patch)].most_common(1)[0][0]
        patch_edges.append(PatchEdge(
            _from=patch_doc_id(from_patch),
            _to=patch_doc_id(to_patch),
            edge_type="PATCH_DEPENDS_ON",
            action_weight=float(weight_counts[(from_patch, to_patch)]),
            affinity=float(count / denom) if denom else 0.0,
            cartan_proxy_sector=sector,
            patch_run_id=run_id,
            from_patch_id=from_patch,
            to_patch_id=to_patch,
            transport_count=int(count),
        ))
    return patch_edges

def build_patches(
    nodes: dict[str, dict], 
    edges: list[dict], 
    fingerprints: dict[str, dict],
    run_id: str,
    *,
    ego_limit: int = 40,
    ego_radius: int = 2,
    min_scc_size: int = 2,
    binder_min_size: int = 3,
    max_patch_nodes: int = 128,
    spectral_k: int = 8,
) -> tuple[list[ChiralPatch], list[PatchMember], list[PatchEdge], list[SpectralSignature]]:
    
    G = nx.DiGraph()
    for node_id, row in nodes.items():
        G.add_node(node_id, **row)
    for e in edges:
        src = e.get("_from")
        dst = e.get("_to")
        if src and dst:
            G.add_edge(src, dst, **e)
        
    patches = []
    members = []
    p_edges = []
    signatures = []
    patch_membership: dict[str, set[str]] = {}
    
    def coarse_hash_for(patch_type: str, node_ids: Iterable[str], hist: list[int], cartan: dict[str, int]) -> str:
        payload = {
            "patch_type": patch_type,
            "level": 2,
            "member_ids": sorted(node_ids),
            "debruijn_histogram": hist,
            "cartan_proxy_histogram": dict(sorted(cartan.items())),
        }
        return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

    def add_internal_patch_edges(patch_id: str, sub_G: nx.DiGraph) -> None:
        for u, v, data in sub_G.edges(data=True):
            p_edges.append(PatchEdge(
                _from=patch_doc_id(patch_id),
                _to=patch_doc_id(patch_id),
                edge_type="PATCH_INTERNAL_EDGE",
                action_weight=float(data.get("action_weight", data.get("weight", 1.0)) or 1.0),
                cartan_proxy_sector=cartan_proxy_sector(data),
                patch_run_id=run_id,
                from_patch_id=patch_id,
                to_patch_id=patch_id,
            ))

    # 1. SCC Patches
    sccs = list(nx.strongly_connected_components(G))
    for i, scc in enumerate(sccs):
        if len(scc) < min_scc_size:
            continue # skip isolated
        
        seed_hash = hashlib.sha256(json.dumps(sorted(list(scc)), sort_keys=True).encode()).hexdigest()[:16]
        patch_id = stable_key(f"{run_id}__scc_patch__{seed_hash}")
        sub_G = G.subgraph(scc)
        
        entropy, bias, cartan = compute_chiral_metrics(sub_G)
        evs, nullity, logdet, spectral_status = compute_spectral_signature(
            sub_G.to_undirected(), k=spectral_k, max_exact_nodes=max_patch_nodes)
        
        hist, redex_density, max_depth = fingerprint_features(scc, fingerprints)
        
        patch = ChiralPatch(
            _key=patch_id,
            patch_id=patch_id,
            patch_type="scc_patch",
            run_id=run_id,
            node_count=len(scc),
            edge_count=sub_G.number_of_edges(),
            coarse_hash="sha256:" + coarse_hash_for("scc_patch", scc, hist, cartan),
            debruijn_histogram=hist,
            chiral_entropy=entropy,
            chiral_bias=bias,
            cartan_proxy_histogram=cartan,
            patch_run_id=run_id,
            cartan_proxy_sector=dominant_cartan_sector(cartan),
            redex_density=redex_density,
            max_debruijn_depth=max_depth,
        )
        patches.append(patch)
        
        signatures.append(SpectralSignature(
            _key=patch_id,
            patch_id=patch_id,
            eigenvalues=evs,
            nullity=nullity,
            pseudo_logdet=logdet,
            patch_run_id=run_id,
            run_id=run_id,
            spectral_status=spectral_status,
        ))
        
        patch_membership[patch_id] = set(scc)
        for node_id in scc:
            members.append(PatchMember(
                _from=patch_doc_id(patch_id),
                _to=node_id,
                membership_type="scc_member",
                patch_run_id=run_id,
                patch_id=patch_id,
            ))
        add_internal_patch_edges(patch_id, sub_G)
            
    # 2. Ego Patches (around high degree nodes)
    undirected = G.to_undirected()
    degrees = sorted(G.degree(), key=lambda x: x[1], reverse=True)
    for node_id, deg in degrees[:ego_limit]:
        ego_nodes = sorted(nx.ego_graph(undirected, node_id, radius=ego_radius).nodes())
        if len(ego_nodes) > max_patch_nodes:
            local_degrees = dict(G.degree(ego_nodes))
            ego_nodes = sorted(sorted(ego_nodes, key=lambda n: (-local_degrees.get(n, 0), str(n)))[:max_patch_nodes])
            if node_id not in ego_nodes:
                ego_nodes = sorted([node_id] + ego_nodes[:-1])
        if len(ego_nodes) < 3: continue
        seed_hash = hashlib.sha256(json.dumps(ego_nodes, sort_keys=True).encode()).hexdigest()[:16]
        patch_id = stable_key(f"{run_id}__ego_patch__{seed_hash}")
        
        sub_G = G.subgraph(ego_nodes)
        entropy, bias, cartan = compute_chiral_metrics(sub_G)
        evs, nullity, logdet, spectral_status = compute_spectral_signature(
            sub_G.to_undirected(), k=spectral_k, max_exact_nodes=max_patch_nodes)
        
        hist, redex_density, max_depth = fingerprint_features(ego_nodes, fingerprints)
                
        patch = ChiralPatch(
            _key=patch_id,
            patch_id=patch_id,
            patch_type="ego_patch",
            run_id=run_id,
            node_count=len(ego_nodes),
            edge_count=sub_G.number_of_edges(),
            coarse_hash="sha256:" + coarse_hash_for("ego_patch", ego_nodes, hist, cartan),
            debruijn_histogram=hist,
            chiral_entropy=entropy,
            chiral_bias=bias,
            cartan_proxy_histogram=cartan,
            patch_run_id=run_id,
            cartan_proxy_sector=dominant_cartan_sector(cartan),
            redex_density=redex_density,
            max_debruijn_depth=max_depth,
        )
        patches.append(patch)
        
        signatures.append(SpectralSignature(
            _key=patch_id,
            patch_id=patch_id,
            eigenvalues=evs,
            nullity=nullity,
            pseudo_logdet=logdet,
            patch_run_id=run_id,
            run_id=run_id,
            spectral_status=spectral_status,
        ))
        
        patch_membership[patch_id] = set(ego_nodes)
        for nid in ego_nodes:
            members.append(PatchMember(
                _from=patch_doc_id(patch_id),
                _to=nid,
                membership_type="ego_member",
                local_role="seed" if nid == node_id else "member",
                patch_run_id=run_id,
                patch_id=patch_id,
            ))
        add_internal_patch_edges(patch_id, sub_G)

    # 3. Binder/fingerprint pattern patches.
    buckets: dict[str, list[str]] = defaultdict(list)
    for node_id, row in fingerprints.items():
        bucket, _meta = fingerprint_bucket(row)
        buckets[bucket].append(node_id)
    for bucket, node_ids in sorted(buckets.items(), key=lambda item: (-len(set(item[1])), item[0])):
        unique_nodes = sorted(set(node_ids))
        if len(unique_nodes) < binder_min_size:
            continue
        if len(unique_nodes) > max_patch_nodes:
            local_degrees = dict(G.degree(unique_nodes))
            unique_nodes = sorted(sorted(unique_nodes, key=lambda n: (-local_degrees.get(n, 0), str(n)))[:max_patch_nodes])
        sub_G = G.subgraph(unique_nodes)
        entropy, bias, cartan = compute_chiral_metrics(sub_G)
        evs, nullity, logdet, spectral_status = compute_spectral_signature(
            sub_G.to_undirected(), k=spectral_k, max_exact_nodes=max_patch_nodes)
        hist, redex_density, max_depth = fingerprint_features(unique_nodes, fingerprints)
        seed_hash = hashlib.sha256(json.dumps({"bucket": bucket, "nodes": unique_nodes}, sort_keys=True).encode()).hexdigest()[:16]
        patch_id = stable_key(f"{run_id}__binder_pattern_patch__{seed_hash}")
        patch = ChiralPatch(
            _key=patch_id,
            patch_id=patch_id,
            patch_type="binder_pattern_patch",
            run_id=run_id,
            node_count=len(unique_nodes),
            edge_count=sub_G.number_of_edges(),
            coarse_hash="sha256:" + coarse_hash_for("binder_pattern_patch", unique_nodes, hist, cartan),
            debruijn_histogram=hist,
            chiral_entropy=entropy,
            chiral_bias=bias,
            cartan_proxy_histogram=cartan,
            patch_run_id=run_id,
            cartan_proxy_sector=dominant_cartan_sector(cartan),
            redex_density=redex_density,
            max_debruijn_depth=max_depth,
        )
        patches.append(patch)
        signatures.append(SpectralSignature(
            _key=patch_id,
            patch_id=patch_id,
            eigenvalues=evs,
            nullity=nullity,
            pseudo_logdet=logdet,
            patch_run_id=run_id,
            run_id=run_id,
            spectral_status=spectral_status,
        ))
        patch_membership[patch_id] = set(unique_nodes)
        for nid in unique_nodes:
            members.append(PatchMember(
                _from=patch_doc_id(patch_id),
                _to=nid,
                membership_type="binder_pattern_member",
                patch_run_id=run_id,
                patch_id=patch_id,
            ))
        add_internal_patch_edges(patch_id, sub_G)

    p_edges.extend(build_patch_dependency_edges(edges, patch_membership, run_id))
    return patches, members, p_edges, signatures

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nodes", required=True, type=Path)
    parser.add_argument("--edges", required=True, type=Path)
    parser.add_argument("--fingerprints", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--run-id", default="")
    parser.add_argument("--ego-limit", type=int, default=40)
    parser.add_argument("--ego-radius", "--ego-hop", dest="ego_radius", type=int, default=2)
    parser.add_argument("--min-scc-size", type=int, default=2)
    parser.add_argument("--binder-min-size", type=int, default=3)
    parser.add_argument("--max-patch-nodes", type=int, default=128)
    parser.add_argument("--spectral-k", type=int, default=8)
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()

    # Load Data
    node_data = {}
    with open(args.nodes, "r") as f:
        for line in f:
            row = json.loads(line)
            key = row.get("_id") or row.get("_key") or row.get("id") or row.get("name")
            if key:
                node_data[normalize_node_key(key)] = row
            
    edge_data = []
    with open(args.edges, "r") as f:
        for line in f:
            row = json.loads(line)
            src = normalize_node_key(row.get("_from") or row.get("src"))
            dst = normalize_node_key(row.get("_to") or row.get("dst"))
            if src and dst:
                edge_data.append({**row, "_from": src, "_to": dst})
            
    fingerprint_data = {}
    if args.fingerprints and args.fingerprints.exists():
        with open(args.fingerprints, "r") as f:
            for line in f:
                row = json.loads(line)
                decl_name = row.get("_id") or row.get("_key") or row.get("decl") or row.get("decl_name") or row.get("name")
                if not decl_name:
                    continue
                fingerprint_data[normalize_node_key(decl_name)] = row

    run_id = stable_key(
        os.environ.get("IG_RUN_ID")
        or args.run_id
        or f"patch_run_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"
    )
    
    # Compute Patches
    patches, members, p_edges, signatures = build_patches(
        node_data,
        edge_data,
        fingerprint_data,
        run_id,
        ego_limit=args.ego_limit,
        ego_radius=args.ego_radius,
        min_scc_size=args.min_scc_size,
        binder_min_size=args.binder_min_size,
        max_patch_nodes=args.max_patch_nodes,
        spectral_k=args.spectral_k,
    )
    
    # Metadata Run
    run = PatchRun(
        _key=run_id,
        schema_version=RUN_SCHEMA_VERSION,
        source_graph_hash=hash_input_files([
            args.nodes,
            args.edges,
            args.fingerprints if args.fingerprints and args.fingerprints.exists() else None,
        ]),
        expr_fingerprint_version="expr_fingerprint.v1" if args.fingerprints and args.fingerprints.exists() else "",
        patch_algorithm=ALGORITHM_VERSION,
        created_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        patch_run_id=run_id,
        run_id=run_id,
        algorithm_version=ALGORITHM_VERSION,
        fingerprints_available=bool(args.fingerprints and args.fingerprints.exists()),
    )
    
    # Write Output
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    def write_jsonl(path, data):
        with open(path, "w") as f:
            for item in data:
                f.write(json.dumps(asdict(item) if hasattr(item, "__dataclass_fields__") else item) + "\n")
        if not args.print_json:
            print(f"[chiral-patches] wrote {path}")

    write_jsonl(args.output_dir / "ig_patch_runs.jsonl", [run])
    write_jsonl(args.output_dir / "ig_chiral_patches.jsonl", patches)
    write_jsonl(args.output_dir / "ig_patch_members.jsonl", members)
    write_jsonl(args.output_dir / "ig_patch_edges.jsonl", p_edges)
    write_jsonl(args.output_dir / "ig_patch_spectral_signatures.jsonl", signatures)
    
    if args.print_json:
        summary = {
            "patch_run_id": run_id,
            "run_id": run_id,
            "patch_count": len(patches),
            "member_count": len(members),
            "signature_count": len(signatures),
            "scc_patch_count": sum(1 for p in patches if p.patch_type == "scc_patch"),
            "ego_patch_count": sum(1 for p in patches if p.patch_type == "ego_patch"),
            "binder_pattern_patch_count": sum(1 for p in patches if p.patch_type == "binder_pattern_patch"),
        }
        print(json.dumps(summary, indent=2))
        
    return 0

if __name__ == "__main__":
    sys.exit(main())
