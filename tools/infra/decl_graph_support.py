#!/usr/bin/env python3
"""
⚖️ THE PAULI GRAPH SUPPORT (Authority Bridge)
Truth lives in Lean; structure lives in the graph.

This module provides a unified interface for accessing Lean declaration graph
metadata, with a dual-authority model:
1. Primary: ArangoDB Live DAG (if reachable and configured).
2. Fallback: Local DAG artifacts (artifacts/dag/index).
"""

from __future__ import annotations

import json
import math
import os
import urllib.request
import urllib.error
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

DECL_INDEX_PATH = Path("artifacts/dag/index/decls.jsonl")
EDGE_INDEX_PATH = Path("artifacts/dag/index/edges.jsonl")
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

def load_json(path: Path) -> Any:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))

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

def leaf_name(full_name: str) -> str:
    return full_name.rsplit(".", 1)[-1]

def normalize_decl_file(root: Path, file_value: str | None) -> str | None:
    if not file_value:
        return None
    path = Path(file_value)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(root).as_posix()
        except ValueError:
            return path.as_posix()
    return path.as_posix()

def parse_decl_attrs(attrs: object) -> tuple[str | None, int | None]:
    rep_layer: str | None = None
    rep_depth: int | None = None
    if not isinstance(attrs, list):
        return rep_layer, rep_depth
    for raw in attrs:
        text = str(raw)
        if text.startswith("rep_layer:"):
            rep_layer = text.split(":", 1)[1] or None
        elif text.startswith("rep_depth_nat:"):
            try:
                rep_depth = int(text.split(":", 1)[1])
            except ValueError:
                pass
    return rep_layer, rep_depth

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

def load_decl_graph(root: Path) -> tuple[dict[tuple[str, int, str], str], dict[str, GraphProfile]]:
    decl_rows = load_jsonl(root / DECL_INDEX_PATH)
    edge_rows = load_jsonl(root / EDGE_INDEX_PATH)
    
    # Authority Selection
    arango_data = query_arango_authority()
    if arango_data:
        print(f"[decl-graph-support] Using ArangoDB live authority ({len(arango_data)} nodes)")
    else:
        print("[decl-graph-support] Using local artifact authority (leaky)")

    decl_key_to_full: dict[tuple[str, int, str], str] = {}
    decl_rows_by_name: dict[str, dict[str, Any]] = {}
    kind_by_name: dict[str, str] = {}

    for row in decl_rows:
        full_name = row.get("name")
        if not isinstance(full_name, str):
            continue
        decl_rows_by_name[full_name] = row
        kind_by_name[full_name] = str(row.get("kind") or "")
        file_rel = normalize_decl_file(root, row.get("file"))
        line = row.get("line")
        if isinstance(file_rel, str) and isinstance(line, int):
            decl_key_to_full[(file_rel, line, leaf_name(full_name))] = full_name

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
        rep_layer, rep_depth = parse_decl_attrs(row.get("attrs"))
        kind = str(row.get("kind") or "")
        
        # ⚖️ PAULI REFACTOR: Authority mapping
        if name in arango_data:
            a = arango_data[name]
            rv = a["rv"]
            rt = a["rt"]
            rth = a["rth"]
            reverse_public_fan_in = a["reverse_public_fan_in"]
            descendant_mass = a["descendant_mass"]
            transitive_reverse_reach = a["transitive_reverse_reach"]
            depth = a["depth"]
            scc_size = a["scc_size"]
            is_sink = a["is_sink"]
            significance_present = a["significance_present"]
        else:
            rv = int(reverse_value_users.get(name, 0))
            rt = int(reverse_type_users.get(name, 0))
            rth = int(reverse_theorem_users.get(name, 0))
            reverse_public_fan_in = rth
            descendant_mass = 0
            transitive_reverse_reach = 0
            depth = rep_depth or 0
            scc_size = 1
            is_sink = False
            significance_present = bool(row.get("doc") and len(str(row.get("doc"))) > 20)

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
            file=normalize_decl_file(root, row.get("file")),
            line=int(row["line"]) if isinstance(row.get("line"), int) else None,
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

def resolve_graph_profile(
    *,
    file_rel: str,
    leaf_name_hint: str,
    line: int | None,
    graph_profiles: dict[str, GraphProfile],
    max_line_delta: int = 8,
) -> GraphProfile | None:
    suffix = f".{leaf_name_hint}"
    candidates: list[tuple[int, GraphProfile]] = []
    for full_name, profile in graph_profiles.items():
        if profile.file != file_rel:
            continue
        if not (full_name == leaf_name_hint or full_name.endswith(suffix)):
            continue
        if line is None or profile.line is None:
            candidates.append((0, profile))
            continue
        delta = abs(profile.line - line)
        if delta <= max_line_delta:
            candidates.append((delta, profile))
    if not candidates:
        return None
    candidates.sort(key=lambda item: (item[0], item[1].name))
    return candidates[0][1]
