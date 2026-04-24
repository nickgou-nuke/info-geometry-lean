#!/usr/bin/env python3
"""
⚖️ THE PAULI GRAPH SUPPORT (Authority Bridge)
Truth lives in Lean; structure lives in the graph.

This module provides a unified interface for accessing Lean declaration graph
metadata, with a strict dual-authority model:
1. Primary: ArangoDB Live DAG (Self-Healing: Filled if empty/stale).
2. Fallback: Local Formal DAG (Created and Filled if ArangoDB is down).
"""

from __future__ import annotations

import json
import math
import os
import subprocess
import sys
import urllib.request
import urllib.error
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

# Pathing configuration
DECL_INDEX_PATH = Path("artifacts/dag/index/decls.jsonl")
EDGE_INDEX_PATH = Path("artifacts/dag/index/edges.jsonl")
TOPOLOGY_NODES_PATH = Path("artifacts/dag/index/topology_overlay_nodes.jsonl")
SIGNIFICANCE_INDEX_PATH = Path("reports/theorem-significance.json")

THEOREM_KINDS = {"theorem", "lemma"}
DEFINITION_KINDS = {"def", "opaque", "abbrev"}

ARANGO_URL = os.environ.get("ARANGO_URL", "http://127.0.0.1:8529")
ARANGO_DB = os.environ.get("ARANGO_DB", "infogeometry")

@dataclass(frozen=True)
class GraphProfile:
    name: str
    kind: str
    module: str
    file: str | None
    line: int | None
    rep_layer: str | None
    rep_depth: int | None
    reverse_value_users: int
    reverse_type_users: int
    reverse_theorem_users: int
    reverse_public_fan_in: int
    descendant_mass: int
    transitive_reverse_reach: int
    depth: int
    scc_size: int
    is_sink: bool
    significance_present: bool
    forward_value_theorems: tuple[str, ...]
    forward_value_defs: tuple[str, ...]
    graph_load_bearing_score: float
    structural_role: str

def run_cmd(cmd: list[str], root: Path, label: str):
    print(f"[pauli-authority] {label}...")
    try:
        subprocess.run(cmd, cwd=root, check=True, capture_output=True)
    except subprocess.CalledProcessError as e:
        print(f"[pauli-authority] ERROR: {label} failed: {e.stderr.decode()}", file=sys.stderr)

def ensure_local_artifacts(root: Path):
    """Ensures local formal artifacts exist."""
    index_dir = root / "artifacts" / "dag" / "index"
    index_dir.mkdir(parents=True, exist_ok=True)
    
    # 1. Check/Create Raw Index
    if not (root / DECL_INDEX_PATH).exists() or not (root / EDGE_INDEX_PATH).exists():
        run_cmd(["lake", "script", "run", "dagRefresh"], root, "Creating missing formal DAG index")

    # 2. Check/Create Topology Overlay (Truthful reach/depth)
    if not (root / TOPOLOGY_NODES_PATH).exists():
        run_cmd([
            "python3", "tools/infra/hydrate_arango_topology.py",
            "--input-dir", "artifacts/dag/index",
            "--output-dir", "artifacts/dag/index",
            "--no-strict-lossless"
        ], root, "Filling local formal mirror (topology hydration)")

def request_json(method: str, url: str, payload: Any = None) -> Any:
    body = None if payload is None else json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=body, method=method)
    req.add_header("Accept", "application/json")
    if body:
        req.add_header("Content-Type", "application/json")
    
    with urllib.request.urlopen(req, timeout=10) as resp:
        return json.loads(resp.read().decode("utf-8"))

def query_arango_authority(root: Path) -> dict[str, dict[str, Any]]:
    """Fetch truthful graph statistics from ArangoDB, ensuring it is filled."""
    url = f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/cursor"
    
    # 1. Sanity Check: Is ArangoDB reachable and filled?
    try:
        count_out = request_json("GET", f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/collection/ig_nodes/count")
        live_count = count_out.get("count", 0)
        
        # If DB is empty or missing, fill it from local artifacts
        if live_count < 1000:
            print("[pauli-authority] ArangoDB mirror is empty/stale. Filling from local artifacts...")
            ensure_local_artifacts(root)
            run_cmd([
                "python3", "tools/infra/arango_layered_ingest.py",
                "--input-dir", "artifacts/dag/index",
                "--drop-existing"
            ], root, "Ingesting into ArangoDB authority")
    except (urllib.error.URLError, urllib.error.HTTPError):
        return {}

    # 2. Full Cursor Consumption (No Ignoring)
    query = """
    FOR n IN ig_nodes
      LET rv = LENGTH(FOR e IN ig_edges FILTER e._to == n._id && e.kind == "value" RETURN 1)
      LET rt = LENGTH(FOR e IN ig_edges FILTER e._to == n._id && e.kind == "type" RETURN 1)
      LET rth = LENGTH(FOR e IN ig_edges 
        FILTER e._to == n._id && e.kind == "value"
        LET s = DOCUMENT(e._from)
        FILTER s != null && (s.kind == "theorem" || s.kind == "lemma")
        RETURN 1)
      
      LET scc_edge = FIRST(FOR e IN topology_overlay_edges FILTER e._from == n._id && e.role == "member_of_scc" RETURN e)
      LET scc = scc_edge != null ? DOCUMENT(scc_edge._to) : null
      
      RETURN {
        name: n.name,
        rv: rv,
        rt: rt,
        rth: rth,
        depth: scc != null ? (scc.depth || 0) : 0,
        scc_size: scc != null ? (scc.node_count || 1) : 1,
        is_sink: scc != null ? (scc.downstream_reachable == 0) : true,
        descendant_mass: scc != null ? (scc.downstream_reachable || 0) : 0,
        transitive_reverse_reach: scc != null ? (scc.upstream_reachable || 0) : 0,
        reverse_public_fan_in: rth,
        significance_present: n.doc != null && LENGTH(n.doc) > 20
      }
    """
    try:
        out = request_json("POST", url, {"query": query, "batchSize": 5000})
        results = {row["name"]: row for row in out.get("result", [])}
        
        # Handle pagination (Crucial: DO NOT IGNORE rest of the graph)
        while out.get("hasMore"):
            cursor_id = out["id"]
            out = request_json("PUT", f"{url}/{cursor_id}")
            for row in out.get("result", []):
                results[row["name"]] = row
        return results
    except (urllib.error.URLError, urllib.error.HTTPError, KeyError):
        return {}

def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open(encoding="utf-8") as handle:
        for raw in handle:
            raw = raw.strip()
            if raw:
                rows.append(json.loads(raw))
    return rows

def parse_decl_attrs(attrs: object) -> tuple[str | None, int | None, dict[str, Any]]:
    rep_layer: str | None = None
    rep_depth: int | None = None
    extra: dict[str, Any] = {}
    if not isinstance(attrs, list):
        return rep_layer, rep_depth, extra
    for raw in attrs:
        text = str(raw)
        if text.startswith("rep_layer:"):
            rep_layer = text.split(":", 1)[1] or None
        elif text.startswith("rep_depth_nat:"):
            try:
                rep_depth = int(text.split(":", 1)[1])
            except ValueError:
                pass
        elif ":" in text:
            k, v = text.split(":", 1)
            extra[k] = int(v) if v.isdigit() else v
    return rep_layer, rep_depth, extra

def structural_role_for_profile(**kwargs) -> str:
    kind = kwargs.get("kind", "")
    if kind not in THEOREM_KINDS:
        return "definition" if kind in DEFINITION_KINDS else "declaration"
    rv, rt, rth = kwargs.get("reverse_value_users", 0), kwargs.get("reverse_type_users", 0), kwargs.get("reverse_theorem_users", 0)
    dm = kwargs.get("descendant_mass", 0)
    if rth == 0 and rv == 0 and rt == 0: return "isolated_theorem"
    if rth == 0 and rv == 0: return "type_only_theorem"
    if rth >= 3 or dm >= 10 or rv >= 3: return "load_bearing"
    return "supported_theorem"

def load_decl_graph(root: Path) -> tuple[dict[tuple[str, int, str], str], dict[str, GraphProfile]]:
    # ⚖️ PAULI AUTHORITY: ArangoDB (Auto-Filled) or Local Formal DAG
    arango_data = query_arango_authority(root)
    if arango_data:
        print(f"[pauli-authority] Primary ArangoDB authority ACTIVE ({len(arango_data)} declarations)")
    else:
        print("[pauli-authority] ArangoDB unreachable. Ensuring local formal DAG mirror...")
        ensure_local_artifacts(root)

    decl_rows = load_jsonl(root / DECL_INDEX_PATH)
    edge_rows = load_jsonl(root / EDGE_INDEX_PATH)
    
    decl_key_to_full: dict[tuple[str, int, str], str] = {}
    decl_rows_by_name: dict[str, dict[str, Any]] = {}
    kind_by_name: dict[str, str] = {}

    for row in decl_rows:
        full_name = row.get("name")
        if not full_name: continue
        decl_rows_by_name[full_name] = row
        kind_by_name[full_name] = str(row.get("kind") or "")
        
        file_val = row.get("file")
        if file_val and isinstance(file_val, str):
            try:
                rel = Path(file_val).resolve().relative_to(root).as_posix()
            except ValueError: rel = file_val
            line = row.get("line")
            if isinstance(line, int):
                decl_key_to_full[(rel, line, full_name.rsplit(".", 1)[-1])] = full_name

    reverse_value_users, reverse_type_users, reverse_theorem_users = [defaultdict(int) for _ in range(3)]
    forward_value_theorems, forward_value_defs = [defaultdict(list) for _ in range(2)]

    for edge in edge_rows:
        src, dst, kind = edge.get("src"), edge.get("dst"), edge.get("kind")
        if not src or not dst: continue
        if kind == "value":
            reverse_value_users[dst] += 1
            if kind_by_name.get(dst, "") in THEOREM_KINDS: forward_value_theorems[src].append(dst)
            else: forward_value_defs[src].append(dst)
            if kind_by_name.get(src, "") in THEOREM_KINDS: reverse_theorem_users[dst] += 1
        elif kind == "type": reverse_type_users[dst] += 1

    profiles: dict[str, GraphProfile] = {}
    for name, row in decl_rows_by_name.items():
        rep_layer, rep_depth, extra = parse_decl_attrs(row.get("attrs"))
        
        if name in arango_data:
            a = arango_data[name]
            rv, rt, rth = a["rv"], a["rt"], a["rth"]
            rpf, dm, trr, dp, ss, sk = a["reverse_public_fan_in"], a["descendant_mass"], a["transitive_reverse_reach"], a["depth"], a["scc_size"], a["is_sink"]
            sig_p = a["significance_present"]
        else:
            rv, rt, rth = reverse_value_users[name], reverse_type_users[name], reverse_theorem_users[name]
            rpf, dm, trr = rth, extra.get("descendant_mass_nat", 0), extra.get("upstream_reachable_nat", 0)
            dp, ss, sk = extra.get("depth_nat", rep_depth or 0), extra.get("scc_size_nat", 1), dm == 0
            sig_p = bool(row.get("doc") and len(str(row.get("doc"))) > 20)

        fwd_t, fwd_d = tuple(forward_value_theorems[name]), tuple(forward_value_defs[name])
        role = structural_role_for_profile(kind=row.get("kind", ""), reverse_value_users=rv, reverse_type_users=rt, reverse_theorem_users=rth, descendant_mass=dm)
        
        load_score = round((3.0*rth) + rv + 0.25*rt + 1.5*math.log1p(rpf) + 1.2*math.log1p(dm), 3)
        profiles[name] = GraphProfile(name=name, kind=row.get("kind", ""), module=row.get("module", ""), file=row.get("file"), line=row.get("line"),
                                      rep_layer=rep_layer, rep_depth=rep_depth, reverse_value_users=rv, reverse_type_users=rt, reverse_theorem_users=rth,
                                      reverse_public_fan_in=rpf, descendant_mass=dm, transitive_reverse_reach=trr, depth=dp, scc_size=ss, is_sink=sk,
                                      significance_present=sig_p, forward_value_theorems=fwd_t, forward_value_defs=fwd_d, graph_load_bearing_score=load_score, structural_role=role)

    return decl_key_to_full, profiles

def weak_graph_evidence(p: GraphProfile | None) -> bool:
    return p is None or p.structural_role in {"isolated_theorem", "type_only_theorem"}
