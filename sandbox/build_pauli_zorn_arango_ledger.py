#!/usr/bin/env python3
"""Materialize a complete Arango declaration/edge ledger for the Pauli–Zorn claim family."""
from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

from arango.client import ArangoClient
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "sandbox" / "pauli_zorn_arango_ledger.json"
load_repo_arango_env(ROOT)
client = ArangoClient(hosts=arango_endpoint())
db = client.db(
    arango_database(), username=arango_username(), password=arango_password()
)

CENTRAL = {
    "pauli": ["pauli", "sigma", "σ"],
    "zorn": ["zorn"],
    "octonion": ["octon"],
    "quaternion": ["quatern", "cayley-dickson", "cayleydickson"],
    "peirce": ["peirce"],
}
BRIDGE = {
    "determinant_norm": ["det", "norm", "quadratic", "minkowski", "lightcone", "lightlike", "null"],
    "ladder_projector": ["ladder", "raising", "lowering", "nilpot", "projector", "idempotent"],
    "chirality": ["chiral", "chirality", "gamma5", "gamma_5", "γ5", "γ₅"],
    "tomita_commutant": ["tomita", "commutant", "modular conjugation", "antiunitary"],
    "equivalence": ["equiv", "isomorph", "bijection", "categor", "inflate", "linear equivalence", "algebra equivalence"],
    "triality_g2": ["triality", "g2", "g₂"],
}

def classify(text: str, table: dict[str, list[str]]) -> list[str]:
    low = text.lower()
    return sorted(k for k, terms in table.items() if any(t.lower() in low for t in terms))

# Query every declaration whose name, module, file, or doc contains a central-family term.
all_terms = sorted({t.lower() for values in CENTRAL.values() for t in values})
query = """
FOR d IN decls
  LET hay = LOWER(CONCAT_SEPARATOR(" ", d.name || "", d.module || "", d.file || "", d.doc || ""))
  FILTER LENGTH(FOR t IN @terms FILTER CONTAINS(hay, t) RETURN 1) > 0
  SORT d.file, d.line, d.name
  RETURN d
"""
declarations = list(db.aql.execute(query, bind_vars={"terms": all_terms}, batch_size=2000))

rows = []
ids = []
names = set()
for d in declarations:
    text = " ".join(str(d.get(k, "") or "") for k in ("name", "module", "file", "doc"))
    source = Path(str(d.get("file", "")))
    source_exists = source.exists()
    source_mtime = source.stat().st_mtime if source_exists else None
    row = {
        "id": d.get("_id"),
        "key": d.get("_key"),
        "name": d.get("name"),
        "kind": d.get("kind"),
        "module": d.get("module"),
        "file": d.get("file"),
        "line": d.get("line"),
        "column": d.get("column"),
        "doc": d.get("doc", ""),
        "central_families": classify(text, CENTRAL),
        "bridge_families": classify(text, BRIDGE),
        "shape_hash": (d.get("shapeHash") or {}).get("shapeHash"),
        "type_shape_hash": (d.get("typeFingerprint") or {}).get("shapeHash"),
        "value_shape_hash": (d.get("valueFingerprint") or {}).get("shapeHash"),
        "source_exists": source_exists,
        "source_mtime": source_mtime,
    }
    rows.append(row)
    if d.get("_id"):
        ids.append(d["_id"])
    if d.get("name"):
        names.add(d["name"])

# Capture every indexed edge incident to a candidate declaration. Edge docs carry names,
# so this remains complete even when endpoint IDs are filtered or projections differ.
edge_query = """
FOR e IN edges
  FILTER e.src IN @names OR e.dst IN @names
  SORT e.src, e.kind, e.dst
  RETURN KEEP(e, "_id", "_from", "_to", "src", "dst", "kind")
"""
edges = list(db.aql.execute(edge_query, bind_vars={"names": sorted(names)}, batch_size=5000))

file_counts = Counter(r["file"] for r in rows)
kind_counts = Counter(r["kind"] for r in rows)
central_counts = Counter(f for r in rows for f in r["central_families"])
bridge_counts = Counter(f for r in rows for f in r["bridge_families"])
files = []
for path, count in sorted(file_counts.items(), key=lambda kv: (-kv[1], str(kv[0]))):
    p = Path(str(path))
    files.append({
        "path": path,
        "declaration_count": count,
        "exists": p.exists(),
        "mtime": p.stat().st_mtime if p.exists() else None,
        "sha256": hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None,
    })

collection_counts = list(db.aql.execute("RETURN {decls:LENGTH(decls), edges:LENGTH(edges)}"))[0]
max_source_mtime = max((r["source_mtime"] for r in rows if r["source_mtime"]), default=None)
dag_paths = [ROOT / "artifacts/dag/index/decls.jsonl", ROOT / "artifacts/dag/index/edges.jsonl"]
dag_artifacts = [
    {"path": str(p), "exists": p.exists(), "mtime": p.stat().st_mtime if p.exists() else None,
     "bytes": p.stat().st_size if p.exists() else None}
    for p in dag_paths
]
ledger = {
    "schema": "info-geometry.pauli-zorn-arango-ledger.v1",
    "generated_at": datetime.now(timezone.utc).isoformat(),
    "target": {
        "endpoint": arango_endpoint(),
        "database": arango_database(),
        "collections": ["decls", "edges"],
        "collection_counts": collection_counts,
    },
    "scope": {
        "central_families": CENTRAL,
        "bridge_families": BRIDGE,
        "selection": "all decls where lowercase name/module/file/doc contains any central term",
        "edge_selection": "all edges where src or dst is a selected declaration name",
        "pagination": "Arango cursor batch_size; no LIMIT",
        "truncated": False,
    },
    "freshness": {
        "dag_artifacts": dag_artifacts,
        "max_selected_live_source_mtime": max_source_mtime,
        "stale_against_selected_live_sources": any(
            p.exists() and max_source_mtime and p.stat().st_mtime < max_source_mtime
            for p in dag_paths
        ),
    },
    "summary": {
        "declarations": len(rows),
        "incident_edges": len(edges),
        "files": len(files),
        "kind_counts": dict(kind_counts),
        "central_family_counts": dict(central_counts),
        "bridge_family_counts": dict(bridge_counts),
    },
    "files": files,
    "declarations": rows,
    "incident_edges": edges,
}
OUT.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"out": str(OUT), **ledger["summary"], "freshness": ledger["freshness"]}, indent=2))
