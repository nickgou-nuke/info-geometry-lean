#!/usr/bin/env python3
"""
⚖️ THE PAULI GRAPH SUPPORT (Authority Bridge)
Truth lives in Lean; structure lives in the graph.

This module provides a unified interface for accessing Lean declaration graph
metadata, with a strict dual-authority model:
1. Primary: ArangoDB Live DAG (if reachable).
2. Fallback: Local Formal DAG (Automatic Creation/Refresh if unreachable).
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
from dataclasses import dataclass
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
    print(f"[decl-graph-support] {label}...")
    try:
        subprocess.run(cmd, cwd=root, check=True, capture_output=True)
    except subprocess.CalledProcessError as e:
        print(f"[decl-graph-support] ERROR: {label} failed: {e.stderr.decode()}", file=sys.stderr)

def ensure_local_artifacts(root: Path):
    """Ensures local formal artifacts exist when ArangoDB is unreachable."""
    index_dir = root / "artifacts" / "dag" / "index"
    index_dir.mkdir(parents=True, exist_ok=True)
    
    # 1. Check/Create Raw Index
    if not (root / DECL_INDEX_PATH).exists() or not (root / EDGE_INDEX_PATH).exists():
        run_cmd(["lake", "script", "run", "dagRefresh"], root, "Creating missing DAG index")

    # 2. Check/Create Topology Overlay (Truthful reach/depth)
    if not (root / TOPOLOGY_NODES_PATH).exists():
        run_cmd([
            "python3", "tools/infra/hydrate_arango_topology.py",
            "--input-dir", "artifacts/dag/index",
            "--output-dir", "artifacts/dag/index",
            "--no-strict-lossless"
        ], root, "Hydrating local topology overlay")


def load_json(path: Path) -> Any:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def load_significance_index(path: Path) -> dict[str, dict[str, Any]]:
    payload = load_json(path)
    if not isinstance(payload, list):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for row in payload:
        if not isinstance(row, dict):
            continue
        name = row.get("name")
        if isinstance(name, str):
            out[name] = row
    return out


def as_int(value: Any, default: int = 0) -> int:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    return default


def as_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    return default


def is_repo_root_context(root: Path) -> bool:
    return (
        (root / "tools" / "infra" / "refresh_decl_graph.py").exists()
        and (root / "lean").exists()
    )

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

def query_arango_authority() -> dict[str, dict[str, Any]]:
    """Fetch truthful graph statistics from ArangoDB."""
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
    payload = {"query": query}
    url = f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/cursor"
    req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), method="POST")
    req.add_header("Accept", "application/json")
    req.add_header("Content-Type", "application/json")
    
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            return {row["name"]: row for row in data.get("result", [])}
    except (urllib.error.URLError, urllib.error.HTTPError):
        return {}

def load_local_topology(root: Path) -> dict[str, dict[str, Any]]:
    """Loads SCC metadata from local topology overlay."""
    ensure_local_artifacts(root)
    overlay_nodes = load_jsonl(root / TOPOLOGY_NODES_PATH)
    out: dict[str, dict[str, Any]] = {}
    
    # SCC nodes have keys like "scc_..." and contain a representative name.
    # We need a mapping from member name -> SCC stats.
    # But hydrate_arango_topology also hydrated the RAW nodes in decls.jsonl.
    # Let's check decls.jsonl for SCC attributes first.
    return out

def structural_role_for_profile(
    *,
    kind: str,
    reverse_value_users: int,
    reverse_type_users: int,
    reverse_theorem_users: int,
    reverse_public_fan_in: int,
    descendant_mass: int,
    transitive_reverse_reach: int,
    depth: int,
    is_sink: bool,
    forward_value_theorems: int,
    forward_value_defs: int,
    rep_depth: int | None,
) -> str:
    if kind not in THEOREM_KINDS:
        return "definition" if kind in DEFINITION_KINDS else "declaration"
    if reverse_public_fan_in == 0 and reverse_value_users == 0 and reverse_type_users == 0:
        return "isolated_theorem"
    if reverse_public_fan_in == 0 and reverse_value_users == 0:
        return "type_only_theorem"
    if (
        reverse_public_fan_in <= 1
        and reverse_theorem_users == 0
        and forward_value_theorems <= 1
        and forward_value_defs <= 2
    ):
        return "thin_forwarder"
    if (
        reverse_public_fan_in >= 3
        or descendant_mass >= 10
        or transitive_reverse_reach >= 50
        or reverse_theorem_users > 0
        or reverse_value_users >= 3
    ):
        return "load_bearing"
    if is_sink or (rep_depth is not None and rep_depth >= 4 and depth >= 8):
        return "capstone_endpoint"
    return "supported_theorem"

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
            if v.isdigit():
                extra[k] = int(v)
            elif v.lower() in ("true", "false"):
                extra[k] = v.lower() == "true"
            else:
                extra[k] = v
    return rep_layer, rep_depth, extra

def load_decl_graph(root: Path) -> tuple[dict[tuple[str, int, str], str], dict[str, GraphProfile]]:
    # ⚖️ PAULI AUTHORITY SELECTION
    allow_live = (
        os.environ.get("DECL_GRAPH_ALLOW_LIVE_ARANGO", "1") == "1"
        and is_repo_root_context(root)
        and root.resolve() == Path.cwd().resolve()
    )
    arango_data = query_arango_authority() if allow_live else {}
    if arango_data:
        print(f"[decl-graph-support] Using ArangoDB live authority ({len(arango_data)} nodes)")
    else:
        print("[decl-graph-support] Using local DAG artifact authority")
        if is_repo_root_context(root):
            ensure_local_artifacts(root)

    decl_rows = load_jsonl(root / DECL_INDEX_PATH)
    edge_rows = load_jsonl(root / EDGE_INDEX_PATH)
    significance_by_name = load_significance_index(root / SIGNIFICANCE_INDEX_PATH)

    decl_key_to_full: dict[tuple[str, int, str], str] = {}
    decl_rows_by_name: dict[str, dict[str, Any]] = {}
    kind_by_name: dict[str, str] = {}

    for row in decl_rows:
        full_name = row.get("name")
        if not isinstance(full_name, str):
            continue
        decl_rows_by_name[full_name] = row
        kind_by_name[full_name] = str(row.get("kind") or "")
        
        # Helper for key lookup
        file_val = row.get("file")
        if file_val and isinstance(file_val, str):
            try:
                file_rel = Path(file_val).resolve().relative_to(root).as_posix()
            except ValueError:
                file_rel = file_val
            line = row.get("line")
            if isinstance(line, int):
                leaf = full_name.rsplit(".", 1)[-1]
                decl_key_to_full[(file_rel, line, leaf)] = full_name

    reverse_value_users: dict[str, int] = defaultdict(int)
    reverse_type_users: dict[str, int] = defaultdict(int)
    reverse_theorem_users: dict[str, int] = defaultdict(int)
    forward_value_theorems: dict[str, list[str]] = defaultdict(list)
    forward_value_defs: dict[str, list[str]] = defaultdict(list)

    for edge in edge_rows:
        src = edge.get("src")
        dst = edge.get("dst")
        kind = edge.get("kind")
        if not isinstance(src, str) or not isinstance(dst, str):
            continue
        if kind == "value":
            reverse_value_users[dst] += 1
            dst_kind = kind_by_name.get(dst, "")
            if dst_kind in THEOREM_KINDS:
                forward_value_theorems[src].append(dst)
            else:
                forward_value_defs[src].append(dst)
            if kind_by_name.get(src, "") in THEOREM_KINDS:
                reverse_theorem_users[dst] += 1
        elif kind == "type":
            reverse_type_users[dst] += 1

    profiles: dict[str, GraphProfile] = {}
    for name, row in decl_rows_by_name.items():
        rep_layer, rep_depth, extra = parse_decl_attrs(row.get("attrs"))
        kind = str(row.get("kind") or "")
        
        # ⚖️ PAULI REFACTOR: Primary Authority check
        if name in arango_data:
            a = arango_data[name]
            rv, rt, rth = a["rv"], a["rt"], a["rth"]
            reverse_public_fan_in = a["reverse_public_fan_in"]
            descendant_mass = a["descendant_mass"]
            transitive_reverse_reach = a["transitive_reverse_reach"]
            depth = a["depth"]
            scc_size = a["scc_size"]
            is_sink = a["is_sink"]
            significance_present = a["significance_present"]
        else:
            # Fallback uses locally hydrated topology attributes in 'extra'
            sig = significance_by_name.get(name, {})
            rv = int(reverse_value_users.get(name, 0))
            rt = int(reverse_type_users.get(name, 0))
            rth = int(reverse_theorem_users.get(name, 0))
            reverse_public_fan_in = as_int(sig.get("reverse_public_fan_in"), rth)
            
            # These fields are populated by hydrate_arango_topology.py into the JSONL attrs
            descendant_mass = as_int(sig.get("descendant_mass"), as_int(extra.get("descendant_mass_nat"), 0))
            transitive_reverse_reach = as_int(sig.get("transitive_reverse_reach"), as_int(extra.get("upstream_reachable_nat"), 0))
            depth = as_int(sig.get("depth"), as_int(extra.get("depth_nat"), rep_depth or 0))
            scc_size = as_int(sig.get("scc_size"), as_int(extra.get("scc_size_nat"), 1))
            is_sink = as_bool(sig.get("is_sink"), as_bool(extra.get("is_sink_bool"), descendant_mass == 0))
            significance_present = name in significance_by_name or bool(row.get("doc") and len(str(row.get("doc"))) > 20)

        fwd_theorems = tuple(forward_value_theorems.get(name, []))
        fwd_defs = tuple(forward_value_defs.get(name, []))
        
        role = structural_role_for_profile(
            kind=kind,
            reverse_value_users=rv,
            reverse_type_users=rt,
            reverse_theorem_users=rth,
            reverse_public_fan_in=reverse_public_fan_in,
            descendant_mass=descendant_mass,
            transitive_reverse_reach=transitive_reverse_reach,
            depth=depth,
            is_sink=is_sink,
            forward_value_theorems=len(fwd_theorems),
            forward_value_defs=len(fwd_defs),
            rep_depth=rep_depth,
        )
        
        load_bearing_score = round(
            (3.0 * float(rth))
            + float(rv)
            + 0.25 * float(rt)
            + 1.5 * math.log1p(max(reverse_public_fan_in, 0))
            + 1.2 * math.log1p(max(descendant_mass, 0))
            + 0.5 * math.log1p(len(fwd_theorems)),
            3,
        )
        
        profiles[name] = GraphProfile(
            name=name,
            kind=kind,
            module=str(row.get("module") or ""),
            file=row.get("file"),
            line=row.get("line"),
            rep_layer=rep_layer,
            rep_depth=rep_depth,
            reverse_value_users=rv,
            reverse_type_users=rt,
            reverse_theorem_users=rth,
            reverse_public_fan_in=reverse_public_fan_in,
            descendant_mass=descendant_mass,
            transitive_reverse_reach=transitive_reverse_reach,
            depth=depth,
            scc_size=scc_size,
            is_sink=is_sink,
            significance_present=significance_present,
            forward_value_theorems=fwd_theorems,
            forward_value_defs=fwd_defs,
            graph_load_bearing_score=load_bearing_score,
            structural_role=role,
        )

    return decl_key_to_full, profiles

def weak_graph_evidence(profile: GraphProfile | None) -> bool:
    if profile is None:
        return True
    return profile.structural_role in {"isolated_theorem", "type_only_theorem", "thin_forwarder"}
