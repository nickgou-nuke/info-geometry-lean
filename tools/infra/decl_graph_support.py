#!/usr/bin/env python3
"""
⚖️ THE PAULI DECLARATION GRAPH SUPPORT
Truth lives in Lean; structure lives in the graph.

This module provides high-level GraphProfile objects by combining Lean source
metadata with formal topological evidence from the Pauli Authority Bridge.
"""

from __future__ import annotations

import json
import math
import os
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from tools.infra.pauli_authority_bridge import (
    PauliProfile as GraphProfile,
    get_authority_data,
    ensure_truth_artifacts,
    DECL_INDEX_PATH,
    EDGE_INDEX_PATH,
)

THEOREM_KINDS = {"theorem", "lemma"}
DEFINITION_KINDS = {"def", "opaque", "abbrev"}

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
            if v.isdigit():
                extra[k] = int(v)
            elif v.lower() in ("true", "false"):
                extra[k] = v.lower() == "true"
            else:
                extra[k] = v
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
    arango_data = get_authority_data(root)
    if arango_data:
        print(f"[pauli-authority] Primary ArangoDB authority ACTIVE ({len(arango_data)} declarations)")
    else:
        print("[pauli-authority] ArangoDB unreachable. Ensuring local formal DAG mirror...")
        if (root / "tools" / "infra" / "hydrate_arango_topology.py").exists():
            ensure_truth_artifacts(root)

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
                leaf = full_name.rsplit(".", 1)[-1]
                decl_key_to_full[(rel, line, leaf)] = full_name

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
            dp, ss, sk = extra.get("depth_nat", rep_depth or 0), extra.get("scc_size_nat", 1), bool(extra.get("is_sink_bool", dm == 0))
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
