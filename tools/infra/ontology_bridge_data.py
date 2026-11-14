"""Pure validation and dry-run operations shared by ontology bridge CLIs.

This module owns transformations that can be tested without opening an Arango
or PostgreSQL connection. Connection setup and write policy remain in the CLI
adapters and projection store.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any

_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[1]
for _path in (_HERE, _REPO_ROOT / "src", _REPO_ROOT):
    if str(_path) not in sys.path:
        sys.path.insert(0, str(_path))


def ensure_term_term_table(cur) -> None:
    """Create the Auto-Ontology term relationship table if absent."""
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS term__term (
            src_term_id   text NOT NULL,
            dst_term_id   text NOT NULL,
            kind          text NOT NULL,
            created_at    timestamptz NOT NULL DEFAULT now(),
            PRIMARY KEY (src_term_id, dst_term_id, kind)
        );
        CREATE INDEX IF NOT EXISTS ix_term__term_dst
            ON term__term (dst_term_id);
        CREATE INDEX IF NOT EXISTS ix_term__term_kind
            ON term__term (kind);
        """
    )


def validate_dependency_edges(db, edge_collection: str, decl_collection: str) -> None:
    """Reject untyped, mis-keyed, foreign, or dangling dependency edges."""
    invalid = list(db.aql.execute(
        """
        FOR e IN @@edges
          LET src = IS_STRING(e.src) ? e.src : ""
          LET dst = IS_STRING(e.dst) ? e.dst : ""
          LET expectedFrom = CONCAT(@decls, "/d_", SUBSTRING(SHA256(src), 0, 40))
          LET expectedTo = CONCAT(@decls, "/d_", SUBSTRING(SHA256(dst), 0, 40))
          LET source = DOCUMENT(expectedFrom)
          LET destination = DOCUMENT(expectedTo)
          FILTER src == "" OR dst == "" OR e.kind NOT IN ["type", "value"]
            OR e._from != expectedFrom OR e._to != expectedTo
            OR source == null OR destination == null
            OR source.name != src OR destination.name != dst
          LIMIT 5
          RETURN e._key
        """,
        bind_vars={"@edges": edge_collection, "decls": decl_collection},
    ))
    if invalid:
        raise ValueError(f"invalid dependency edges in {edge_collection!r}: {invalid}")


def _write_report(report_path: str | None, payload: dict[str, Any]) -> None:
    if report_path:
        out = Path(report_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_offline_jsonl_dry_run(args) -> int:
    """Validate declaration/edge JSONL and emit the projection source digest."""
    from igf.graph.decl_schema import decl_key, edge_key
    from decl_projection import DEFAULT_DEPLOYMENT_UUID, Source, source_digest
    from uuid import UUID

    decls_path = Path(args.decls_jsonl)
    if not decls_path.is_file():
        raise SystemExit(f"declarations JSONL file not found: {decls_path}")
    seen_names: set[str] = set()
    decl_by_key: dict[str, dict] = {}
    modules: set[str] = set()
    for line_no, raw in enumerate(decls_path.read_text(encoding="utf-8").splitlines(), start=1):
        text = raw.strip()
        if not text:
            continue
        doc = json.loads(text)
        if not isinstance(doc, dict):
            raise SystemExit(f"{decls_path}:{line_no}: declaration record must be a JSON object")
        name = doc.get("name")
        if not isinstance(name, str) or not name.strip():
            raise SystemExit("declaration source contains a missing name or identity")
        if name in seen_names:
            raise SystemExit("declaration source contains duplicate names")
        seen_names.add(name)
        expected_key = decl_key(name)
        key = doc.get("_key") or doc.get("key") or expected_key
        if key != expected_key:
            raise SystemExit(f"{decls_path}:{line_no}: declaration key mismatch for {name!r}")
        module = doc.get("module") or "Unknown"
        modules.add(module)
        decl_by_key[key] = {**doc, "_key": key, "name": name, "module": module}

    if not decl_by_key:
        raise SystemExit(f"refusing empty declaration import from {str(decls_path)!r}")

    edge_by_key: dict[str, tuple[str, str, str, str, dict]] = {}
    if args.edges_jsonl:
        edges_path = Path(args.edges_jsonl)
        if not edges_path.is_file():
            raise SystemExit(f"edges JSONL file not found: {edges_path}")
        for line_no, raw in enumerate(edges_path.read_text(encoding="utf-8").splitlines(), start=1):
            text = raw.strip()
            if not text:
                continue
            edge = json.loads(text)
            if not isinstance(edge, dict):
                raise SystemExit(f"{edges_path}:{line_no}: edge record must be a JSON object")
            src, dst, kind = edge.get("src"), edge.get("dst"), edge.get("kind")
            if (not isinstance(src, str) or not src or not isinstance(dst, str) or not dst
                    or kind not in ("type", "value")):
                raise SystemExit(f"{edges_path}:{line_no}: invalid dependency edge")
            src_key, dst_key = decl_key(src), decl_key(dst)
            if src_key not in decl_by_key or dst_key not in decl_by_key:
                raise SystemExit(f"{edges_path}:{line_no}: dangling edge endpoint {src!r} -> {dst!r}")
            key = edge.get("_key") or edge.get("key") or edge_key(src, kind, dst)
            if key != edge_key(src, kind, dst):
                raise SystemExit(f"{edges_path}:{line_no}: edge key mismatch")
            payload = {**edge, "_key": key, "src": src, "dst": dst, "kind": kind}
            edge_by_key[key] = (key, src_key, dst_key, kind, payload)

    deployment_uuid = UUID(args.deployment_uuid) if args.deployment_uuid else DEFAULT_DEPLOYMENT_UUID
    source = Source(deployment_uuid, args.arango_db or "infogeometry")
    sorted_decls = [
        (key, decl_by_key[key]["name"], decl_by_key[key]["module"], decl_by_key[key])
        for key in sorted(decl_by_key, key=lambda value: value.encode("utf-8"))
    ]
    sorted_edges = [edge_by_key[key] for key in sorted(edge_by_key, key=lambda value: value.encode("utf-8"))]
    receipt = {
        "_key": args.generation_id or "offline_dry_run",
        "schema": "info_geometry.decl_graph_generation.v1",
        "status": "complete",
        "declarationCount": len(sorted_decls),
        "validEdgeCount": len(sorted_edges),
    }
    digest = source_digest(source, receipt, sorted_decls, sorted_edges)
    report = {
        "status": "dry_run_ok",
        "mode": "offline_jsonl",
        "generation_id": args.generation_id or "offline_dry_run",
        "source_id": str(deployment_uuid),
        "arango_database": source.arango_database,
        "expected_decl_count": len(sorted_decls),
        "loaded_decl_count": 0,
        "expected_edge_count": len(sorted_edges),
        "loaded_edge_count": 0,
        "module_count": len(modules),
        "source_digest": digest,
    }
    _write_report(args.report_json, report)
    print(json.dumps(report, sort_keys=True))
    return 0
