#!/usr/bin/env python3
"""
Build coarse-grained chiral patches over the declaration graph.
Implements the v1.1 specification for Level 2 spectral navigation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

import networkx as nx
import numpy as np
from scipy.sparse import csr_matrix

# --- Schema and Policy ---
SCHEMA_VERSION = "ig.chiral_patch.v1.1"

# --- Data Structures ---

@dataclass
class PatchRun:
    _key: str
    schema_version: str
    source_graph_hash: str
    expr_fingerprint_version: str
    patch_algorithm: str
    created_at: str

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

@dataclass
class PatchMember:
    _from: str
    _to: str
    membership_type: str
    local_role: str = "member"

@dataclass
class PatchEdge:
    _from: str
    _to: str
    edge_type: str = "PATCH_DEPENDS_ON"
    action_weight: float = 1.0
    affinity: float = 0.0
    cartan_proxy_sector: str = "unknown"

@dataclass
class SpectralSignature:
    _key: str
    patch_id: str
    eigenvalues: list[float]
    nullity: int
    pseudo_logdet: float

# --- Core Logic ---

def compute_spectral_signature(G: nx.Graph, k: int = 10) -> tuple[list[float], int, float]:
    if G.number_of_nodes() < 2:
        return [], 0, 0.0
    
    try:
        L = nx.normalized_laplacian_matrix(G).toarray()
        evals = np.linalg.eigvalsh(L)
        evals = np.sort(evals)
        
        # Nullity (count eigenvalues near zero)
        nullity = int(np.sum(evals < 1e-10))
        
        # Non-zero eigenvalues for logdet
        nonzero = evals[evals > 1e-10]
        pseudo_logdet = float(np.sum(np.log(nonzero))) if nonzero.size > 0 else 0.0
        
        # Top k nonzero eigenvalues (bucketed/truncated)
        signature_vals = [round(float(v), 4) for v in nonzero[:k]]
        
        return signature_vals, nullity, pseudo_logdet
    except Exception:
        return [], 0, 0.0

def compute_chiral_metrics(sub_G: nx.DiGraph) -> tuple[float, float, dict[str, int]]:
    forward = 0
    backward = 0
    mixed = 0
    
    cartan_counts = Counter()
    
    for u, v, d in sub_G.edges(data=True):
        direction = d.get("time_direction", "forward")
        if direction == "forward":
            forward += 1
        elif direction == "backward":
            backward += 1
        else:
            mixed += 1
            
        sector = d.get("cartan_proxy_sector", "unknown")
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
    
    return float(entropy), float(bias), dict(cartan_counts)

def build_patches(
    nodes: dict[str, dict], 
    edges: list[dict], 
    fingerprints: dict[str, dict],
    run_id: str
) -> tuple[list[ChiralPatch], list[PatchMember], list[PatchEdge], list[SpectralSignature]]:
    
    G = nx.DiGraph()
    for e in edges:
        # Map src/dst to ig_nodes format
        src = f"ig_nodes/{e['src']}" if 'src' in e else e.get('_from')
        dst = f"ig_nodes/{e['dst']}" if 'dst' in e else e.get('_to')
        if src and dst:
            G.add_edge(src, dst, **e)
        
    patches = []
    members = []
    p_edges = []
    signatures = []
    
    # 1. SCC Patches
    sccs = list(nx.strongly_connected_components(G))
    for i, scc in enumerate(sccs):
        if len(scc) < 2: continue # skip isolated
        
        patch_id = f"patch_scc_{run_id}_{i}"
        sub_G = G.subgraph(scc)
        
        entropy, bias, cartan = compute_chiral_metrics(sub_G)
        evs, nullity, logdet = compute_spectral_signature(sub_G.to_undirected())
        
        # Aggregate De Bruijn
        hist = np.zeros(10, dtype=int)
        for node_id in scc:
            f = fingerprints.get(node_id, {})
            h = f.get("depthHistogram", [])
            for j, val in enumerate(h[:10]):
                hist[j] += val
        
        patch = ChiralPatch(
            _key=patch_id,
            patch_id=patch_id,
            patch_type="scc_patch",
            run_id=run_id,
            node_count=len(scc),
            edge_count=sub_G.number_of_edges(),
            coarse_hash=hashlib.sha256(json.dumps(sorted(list(scc))).encode()).hexdigest()[:16],
            debruijn_histogram=hist.tolist(),
            chiral_entropy=entropy,
            chiral_bias=bias,
            cartan_proxy_histogram=cartan
        )
        patches.append(patch)
        
        signatures.append(SpectralSignature(
            _key=patch_id,
            patch_id=patch_id,
            eigenvalues=evs,
            nullity=nullity,
            pseudo_logdet=logdet
        ))
        
        for node_id in scc:
            members.append(PatchMember(_from=f"ig_chiral_patches/{patch_id}", _to=node_id, membership_type="scc"))
            
    # 2. Ego Patches (around high degree nodes)
    degrees = sorted(G.degree(), key=lambda x: x[1], reverse=True)
    for node_id, deg in degrees[:20]: # Top 20 hubs
        patch_id = f"patch_ego_{run_id}_{node_id.split('/')[-1]}"
        ego_nodes = nx.ego_graph(G, node_id, radius=2).nodes()
        if len(ego_nodes) < 3: continue
        
        sub_G = G.subgraph(ego_nodes)
        entropy, bias, cartan = compute_chiral_metrics(sub_G)
        evs, nullity, logdet = compute_spectral_signature(sub_G.to_undirected())
        
        # Aggregate De Bruijn
        hist = np.zeros(10, dtype=int)
        for nid in ego_nodes:
            f = fingerprints.get(nid, {})
            h = f.get("depthHistogram", [])
            for j, val in enumerate(h[:10]):
                hist[j] += val
                
        patch = ChiralPatch(
            _key=patch_id,
            patch_id=patch_id,
            patch_type="ego_patch",
            run_id=run_id,
            node_count=len(ego_nodes),
            edge_count=sub_G.number_of_edges(),
            coarse_hash=hashlib.sha256(json.dumps(sorted(list(ego_nodes))).encode()).hexdigest()[:16],
            debruijn_histogram=hist.tolist(),
            chiral_entropy=entropy,
            chiral_bias=bias,
            cartan_proxy_histogram=cartan
        )
        patches.append(patch)
        
        signatures.append(SpectralSignature(
            _key=patch_id,
            patch_id=patch_id,
            eigenvalues=evs,
            nullity=nullity,
            pseudo_logdet=logdet
        ))
        
        for nid in ego_nodes:
            members.append(PatchMember(_from=f"ig_chiral_patches/{patch_id}", _to=nid, membership_type="ego"))

    return patches, members, p_edges, signatures

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nodes", required=True, type=Path)
    parser.add_argument("--edges", required=True, type=Path)
    parser.add_argument("--fingerprints", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()

    # Load Data
    node_data = {}
    with open(args.nodes, "r") as f:
        for line in f:
            row = json.loads(line)
            key = row.get('_key') or row.get('name')
            if key:
                node_data[f"ig_nodes/{key}"] = row
            
    edge_data = []
    with open(args.edges, "r") as f:
        for line in f:
            edge_data.append(json.loads(line))
            
    fingerprint_data = {}
    if args.fingerprints and args.fingerprints.exists():
        with open(args.fingerprints, "r") as f:
            for line in f:
                row = json.loads(line)
                decl_name = row.get('decl') or row.get('decl_name') or row.get('name')
                if not decl_name:
                    continue
                fingerprint_data[f"ig_nodes/{decl_name}"] = row

    run_id = f"run_{int(time.time())}"
    
    # Compute Patches
    patches, members, p_edges, signatures = build_patches(node_data, edge_data, fingerprint_data, run_id)
    
    # Metadata Run
    run = PatchRun(
        _key=run_id,
        schema_version=SCHEMA_VERSION,
        source_graph_hash=hashlib.sha256(args.edges.read_bytes()).hexdigest()[:16],
        expr_fingerprint_version="expr_fingerprint.v1",
        patch_algorithm="chiral_patch_hashes.v1.1",
        created_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    )
    
    # Write Output
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    def write_jsonl(path, data):
        with open(path, "w") as f:
            for item in data:
                f.write(json.dumps(asdict(item) if hasattr(item, "__dataclass_fields__") else item) + "\n")
        print(f"[chiral-patches] wrote {path}")

    write_jsonl(args.output_dir / "ig_patch_runs.jsonl", [run])
    write_jsonl(args.output_dir / "ig_chiral_patches.jsonl", patches)
    write_jsonl(args.output_dir / "ig_patch_members.jsonl", members)
    write_jsonl(args.output_dir / "ig_patch_edges.jsonl", p_edges)
    write_jsonl(args.output_dir / "ig_patch_spectral_signatures.jsonl", signatures)
    
    if args.print_json:
        summary = {
            "run_id": run_id,
            "patch_count": len(patches),
            "member_count": len(members),
            "signature_count": len(signatures)
        }
        print(json.dumps(summary, indent=2))
        
    return 0

if __name__ == "__main__":
    sys.exit(main())
