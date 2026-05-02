#!/usr/bin/env python3
"""
⚖️ THE PAULI AUTHORITY BRIDGE
Truth lives in Lean; structure lives in the graph.

This module is the sole source of structural truth for the reporting suite.
It implements the 'Creation-on-Failure' and 'Self-Healing' authority model.
"""

from __future__ import annotations

import base64
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

# Registry of Truth
DECL_INDEX_PATH = Path("artifacts/dag/index/decls.jsonl")
EDGE_INDEX_PATH = Path("artifacts/dag/index/edges.jsonl")
TOPOLOGY_NODES_PATH = Path("artifacts/dag/index/topology_overlay_nodes.jsonl")

ARANGO_URL = os.environ.get("ARANGO_URL", "http://127.0.0.1:8530")
ARANGO_DB = os.environ.get("ARANGO_DB", "infogeometry")
ARANGO_USER = os.environ.get("ARANGO_USER", os.environ.get("ARANGO_USERNAME", "root"))
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")

def _arango_auth_header() -> str | None:
    if ARANGO_PASSWORD == "" and ARANGO_USER == "":
        return None
    token = base64.b64encode(f"{ARANGO_USER}:{ARANGO_PASSWORD}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"

def _repo_context_allows_live_authority(root: Path) -> bool:
    if os.environ.get("DECL_GRAPH_ALLOW_LIVE_ARANGO", "1") != "1":
        return False
    return (
        (root / "tools" / "infra" / "arango_layered_ingest.py").exists()
        and (root / "lean").exists()
    )

@dataclass(frozen=True)
class PauliProfile:
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
    print(f"[pauli-bridge] {label}...")
    try:
        subprocess.run(cmd, cwd=root, check=True, capture_output=True)
    except subprocess.CalledProcessError as e:
        print(f"[pauli-bridge] ERROR: {label} failed: {e.stderr.decode()}", file=sys.stderr)

def ensure_truth_artifacts(root: Path):
    """Ensures local formal artifacts exist and are filled."""
    index_dir = root / "artifacts" / "dag" / "index"
    index_dir.mkdir(parents=True, exist_ok=True)

    if not (root / DECL_INDEX_PATH).exists() or not (root / EDGE_INDEX_PATH).exists():
        run_cmd(["lake", "script", "run", "dagRefresh"], root, "Regenerating formal DAG index")

    if not (root / TOPOLOGY_NODES_PATH).exists():
        run_cmd([
            "python3", "tools/infra/hydrate_arango_topology.py",
            "--input-dir", "artifacts/dag/index",
            "--output-dir", "artifacts/dag/index",
            "--no-strict-lossless"
        ], root, "Hydrating formal topology overlay")


def _jsonl_line_count(path: Path) -> int:
    if not path.exists():
        return 0
    with path.open(encoding="utf-8") as handle:
        return sum(1 for line in handle if line.strip())

def get_authority_data(root: Path) -> dict[str, dict[str, Any]]:
    """Fetch truthful data from ArangoDB, self-healing if needed."""
    if not _repo_context_allows_live_authority(root):
        return {}

    url = f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/cursor"

    try:
        # Check if DB is reachable, then validate live mirror freshness against local DAG artifacts.
        req = urllib.request.Request(f"{ARANGO_URL.rstrip('/')}/_db/{ARANGO_DB}/_api/collection/ig_nodes/count")
        auth = _arango_auth_header()
        if auth:
            req.add_header("Authorization", auth)
        with urllib.request.urlopen(req, timeout=5) as resp:
            live_count = json.loads(resp.read().decode("utf-8")).get("count", 0)

        ensure_truth_artifacts(root)
        local_decl_count = _jsonl_line_count(root / DECL_INDEX_PATH)

        # Self-heal empty mirrors. Coverage mismatches are handled downstream
        # by deterministic fallback to the fully hydrated local mirror.
        if live_count < 1000:
            print("[pauli-bridge] ArangoDB mirror empty. Re-ingesting authoritative local DAG artifacts...")
            run_cmd([
                "python3", "tools/infra/arango_layered_ingest.py",
                "--input-dir", "artifacts/dag/index",
                "--drop-existing"
            ], root, "Populating ArangoDB authority")
        elif local_decl_count > 0 and live_count != local_decl_count:
            print(
                "[pauli-bridge] Live/local declaration counts differ "
                f"(live={live_count}, local={local_decl_count}); "
                "reporting layer will enforce full-coverage local fallback when needed."
            )
    except (urllib.error.URLError, urllib.error.HTTPError):
        return {}

    # Query with full pagination
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
        name: n.name, rv: rv, rt: rt, rth: rth,
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
        body = json.dumps({"query": query, "batchSize": 5000}).encode("utf-8")
        req = urllib.request.Request(url, data=body, method="POST")
        req.add_header("Content-Type", "application/json")
        auth = _arango_auth_header()
        if auth:
            req.add_header("Authorization", auth)
        with urllib.request.urlopen(req, timeout=15) as resp:
            out = json.loads(resp.read().decode("utf-8"))
            results = {row["name"]: row for row in out.get("result", [])}
            while out.get("hasMore"):
                req = urllib.request.Request(f"{url}/{out['id']}", method="PUT")
                auth = _arango_auth_header()
                if auth:
                    req.add_header("Authorization", auth)
                with urllib.request.urlopen(req, timeout=15) as resp:
                    out = json.loads(resp.read().decode("utf-8"))
                    for row in out.get("result", []):
                        results[row["name"]] = row
            return results
    except Exception:
        return {}
