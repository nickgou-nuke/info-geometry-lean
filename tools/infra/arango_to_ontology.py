#!/usr/bin/env python3
"""
Bridge: ArangoDB (info-geometry-lean declaration graph) -> Auto-Ontology Postgres ontology store.

Reads Lean declarations from ArangoDB (or offline JSONL in --dry-run mode) and writes them
as Auto-Ontology ``term`` rows (source='semantic'), grouped by Lean module into ``catalog_table``
rows linked via ``table__term`` edges, with optional generation-pinned snapshot storage and
atomic CAS promotion in schema ``ig_decl_projection``.
"""
from __future__ import annotations

import argparse
import csv
import io
import json
import os
from pathlib import Path
import sys
from datetime import datetime, timezone
from uuid import UUID

_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[1]
for _p in (_HERE, _REPO_ROOT / "src", _REPO_ROOT):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

try:
    import psycopg
except ImportError:  # pragma: no cover - offline/dry-run environments without psycopg
    psycopg = None  # type: ignore[assignment]
try:
    from arango import ArangoClient
except ImportError:  # pragma: no cover - offline/dry-run environments without python-arango
    ArangoClient = None  # type: ignore[assignment,misc]
from decl_graph_generation import resolve_decl_graph_generation, validate_generation_id
from ontology_bridge_common import refresh_legacy_pg_connect, resolve_arango_env
from ontology_bridge_data import (
    ensure_term_term_table,
    run_offline_jsonl_dry_run,
    validate_dependency_edges,
)


ARANGO_ENDPOINT = os.environ.get("ARANGO_ENDPOINT", "")
ARANGO_DATABASE = os.environ.get("ARANGO_DATABASE", "")
ARANGO_USER = os.environ.get("ARANGO_USER", "")
ARANGO_PASS = os.environ.get("ARANGO_PASS", "")

PG_CONNECT = {
    "user": os.environ.get("POSTGRES_USER", ""),
    "password": os.environ.get("POSTGRES_PASSWORD", ""),
    "host": os.environ.get("POSTGRES_HOST", "localhost"),
    "port": os.environ.get("POSTGRES_PORT", "5433"),
    "dbname": os.environ.get("POSTGRES_DATABASE", "auto_ontology"),
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _resolve_arango_env(database_override: str | None = None) -> tuple[str, str, str, str]:
    return resolve_arango_env(database_override)


def get_pg_connect() -> dict[str, str]:
    return refresh_legacy_pg_connect(PG_CONNECT)


def connect_arango(database: str):
    endpoint, db_name, user, password = _resolve_arango_env(database)
    client = ArangoClient(hosts=endpoint)
    return client.db(
        db_name, username=user, password=password, verify=True
    )


def ensure_catalog(cur, db_name: str) -> str:
    cur.execute(
        "INSERT INTO catalog_database (name, dialect, description, pulled) "
        "VALUES (%s, %s, %s, %s) "
        "ON CONFLICT (name) DO UPDATE SET pulled = EXCLUDED.pulled "
        "RETURNING id",
        (db_name, "lean", "info-geometry-lean Lean declaration graph", now_iso()),
    )
    return cur.fetchone()[0]


def ensure_schema(cur, db_id: str, schema_name: str = "lean") -> str:
    cur.execute(
        "INSERT INTO catalog_schema (database_id, name, description) "
        "VALUES (%s, %s, %s) "
        "ON CONFLICT (database_id, name) DO UPDATE SET description = EXCLUDED.description "
        "RETURNING id",
        (db_id, schema_name, "Lean source modules"),
    )
    return cur.fetchone()[0]


def upsert_modules(cur, schema_id: str, modules: list[str]) -> dict[str, str]:
    if not modules:
        return {}
    result: dict[str, str] = {}
    for m in modules:
        cur.execute(
            "INSERT INTO catalog_table (schema_id, name, table_type, description) "
            "VALUES (%s, %s, %s, %s) "
            "ON CONFLICT (schema_id, name) DO UPDATE SET description = EXCLUDED.description "
            "RETURNING id",
            (schema_id, m, "lean_module", f"Lean module {m}"),
        )
        result[m] = cur.fetchone()[0]
    return result


def copy_terms(cur, terms: list[dict]) -> dict[str, str]:
    """Bulk upsert terms via a temp staging table + COPY. Return imported_id->term id."""
    if not terms:
        return {}
    cur.execute("DROP TABLE IF EXISTS pg_temp.term_staging")
    cur.execute(
        "CREATE TEMP TABLE term_staging (LIKE term INCLUDING DEFAULTS) ON COMMIT DROP"
    )
    buf = io.StringIO()
    writer = csv.writer(buf)
    for t in terms:
        syn = "{" + ",".join(t["synonyms"]) + "}" if t["synonyms"] else "{}"
        writer.writerow([
            t["name"],
            t["description"],
            "semantic",
            syn,
            t["aokey"],
        ])
    buf.seek(0)
    with cur.copy(
        "COPY term_staging (name, description, source, synonyms, imported_id) "
        "FROM STDIN WITH (FORMAT csv)"
    ) as copy:
        copy.write(buf.read())
    cur.execute(
        "INSERT INTO term (name, description, source, synonyms, imported_id) "
        "SELECT name, description, source, synonyms, imported_id FROM term_staging "
        "ON CONFLICT (name, source) DO UPDATE SET "
        "  description = EXCLUDED.description, "
        "  synonyms = EXCLUDED.synonyms, "
        "  imported_id = EXCLUDED.imported_id, "
        "  modified = now() "
        "RETURNING id, imported_id"
    )
    result: dict[str, str] = {}
    for tid, imp_id in cur.fetchall():
        if not tid or imp_id in result:
            raise ValueError("term upsert returned a missing or ambiguous identity")
        result[imp_id] = tid
    expected = {term["aokey"] for term in terms}
    if len(expected) != len(terms) or set(result) != expected:
        raise ValueError("term upsert did not resolve every declaration exactly once")
    return result


def link_table_terms(cur, pairs: list[tuple[str, str]]) -> None:
    if not pairs:
        return
    cur.execute("DROP TABLE IF EXISTS pg_temp.link_staging")
    cur.execute(
        "CREATE TEMP TABLE link_staging (table_id text, term_id text) ON COMMIT DROP"
    )
    buf = io.StringIO()
    writer = csv.writer(buf)
    for table_id, term_id in pairs:
        writer.writerow([table_id, term_id])
    buf.seek(0)
    with cur.copy("COPY link_staging (table_id, term_id) FROM STDIN WITH (FORMAT csv)") as copy:
        copy.write(buf.read())
    cur.execute(
        "INSERT INTO table__term (table_id, term_id) "
        "SELECT table_id, term_id FROM link_staging "
        "ON CONFLICT DO NOTHING"
    )


def _write_report(report_path: str | None, payload: dict) -> None:
    if report_path:
        out = Path(report_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run_offline_jsonl_dry_run(args) -> int:
    """Compatibility wrapper for the shared offline projection validator."""
    return run_offline_jsonl_dry_run(args)


def _run_pinned_generation_projection(args, db, generation: dict, decl_collection: str, total: int) -> int:
    from igf.graph.decl_schema import decl_key
    from decl_projection import (
        DEFAULT_DEPLOYMENT_UUID,
        ProjectionStore,
        Source,
        source_digest,
    )
    edge_collection = generation["edgeCollection"]
    if not edge_collection.replace("_", "").isalnum():
        raise SystemExit(f"unsafe edge collection name: {edge_collection!r}")
    validate_dependency_edges(db, edge_collection, decl_collection)

    dep_uuid = UUID(args.deployment_uuid) if args.deployment_uuid else DEFAULT_DEPLOYMENT_UUID
    source = Source(dep_uuid, args.arango_db or "infogeometry")

    decl_docs = list(db.aql.execute(
        f"FOR d IN {decl_collection} SORT d._key RETURN d",
        batch_size=args.batch_size,
    ))
    if len(decl_docs) != total:
        raise SystemExit(f"incomplete declaration stream: got {len(decl_docs)}, expected {total}")

    normalized_decls: list[dict] = []
    modules: set[str] = set()
    for d in decl_docs:
        clean = {k: v for k, v in d.items() if k not in ("_id", "_rev")}
        mod = clean.get("module") or "Unknown"
        clean["module"] = mod
        modules.add(mod)
        normalized_decls.append(clean)
    normalized_decls.sort(key=lambda d: d["_key"].encode("utf-8"))

    edge_docs = list(db.aql.execute(
        f"FOR e IN {edge_collection} SORT e._key RETURN e",
        batch_size=args.batch_size,
    ))
    expected_edges = generation.get("validEdgeCount", len(edge_docs))
    if len(edge_docs) != expected_edges:
        raise SystemExit(f"incomplete edge stream: got {len(edge_docs)}, expected {expected_edges}")

    normalized_edges: list[dict] = []
    for e in edge_docs:
        clean_e = {k: v for k, v in e.items() if k not in ("_id", "_rev")}
        normalized_edges.append(clean_e)
    normalized_edges.sort(key=lambda e: e["_key"].encode("utf-8"))

    digest_decls = [(d["_key"], d["name"], d["module"], d) for d in normalized_decls]
    digest_edges = [
        (e["_key"], decl_key(e["src"]), decl_key(e["dst"]), e["kind"], e)
        for e in normalized_edges
    ]
    receipt = {k: v for k, v in generation.items() if k not in ("_id", "_rev")}
    receipt["_key"] = args.generation_id
    expected_digest = source_digest(source, receipt, digest_decls, digest_edges)

    if args.dry_run:
        report = {
            "status": "dry_run_ok",
            "mode": "arango_generation_pinned",
            "generation_id": args.generation_id,
            "source_id": str(dep_uuid),
            "arango_database": source.arango_database,
            "expected_decl_count": len(normalized_decls),
            "loaded_decl_count": 0,
            "expected_edge_count": len(normalized_edges),
            "loaded_edge_count": 0,
            "module_count": len(modules),
            "source_digest": expected_digest,
        }
        _write_report(args.report_json, report)
        print(json.dumps(report, sort_keys=True))
        return 0

    conn = psycopg.connect(**get_pg_connect())
    try:
        conn.autocommit = False
        cur = conn.cursor()
        db_id = ensure_catalog(cur, source.arango_database)
        schema_id = ensure_schema(cur, db_id)
        ensure_term_term_table(cur)
        module_ids = upsert_modules(cur, schema_id, sorted(modules))
        term_map: dict[str, str] = {}
        for i in range(0, len(normalized_decls), args.batch_size):
            batch_docs = normalized_decls[i : i + args.batch_size]
            pending_terms = []
            for doc in batch_docs:
                rel_file = doc.get("relFile") or ""
                line = doc.get("line") or 0
                desc = doc.get("doc") or ""
                if rel_file:
                    desc += f"\n\nSource: {rel_file}:{line}"
                pending_terms.append({
                    "name": doc["name"],
                    "description": desc,
                    "synonyms": [doc.get("kind") or ""],
                    "aokey": doc["_key"],
                    "module": doc["module"],
                })
            term_map.update(copy_terms(cur, pending_terms))
        cur.close()
        conn.commit()

        conn.autocommit = True
        store = ProjectionStore(conn)
        store.register_source(source, db_id)
        existing = store.find_generation(source, args.generation_id)
        if existing is not None:
            gen_uuid, status, actual_digest = existing
            if status == "complete" and actual_digest == expected_digest:
                sel = store.current_selection(source, receipt["importRoot"], receipt["namespace"])
                report = {
                    "status": "already_complete_noop",
                    "mode": "generation_pinned",
                    "generation_id": args.generation_id,
                    "generation_uuid": str(gen_uuid),
                    "source_id": str(dep_uuid),
                    "arango_database": source.arango_database,
                    "expected_decl_count": len(normalized_decls),
                    "loaded_decl_count": len(normalized_decls),
                    "expected_edge_count": len(normalized_edges),
                    "loaded_edge_count": len(normalized_edges),
                    "module_count": len(module_ids),
                    "source_digest": expected_digest,
                    "active_generation_uuid": str(sel.generation) if sel.generation else None,
                    "revision": sel.revision,
                }
                _write_report(args.report_json, report)
                print(json.dumps(report, sort_keys=True))
                return 0
            raise SystemExit(
                f"generation {args.generation_id!r} already exists with status={status!r} "
                f"and incompatible digest"
            )

        prior_sel = store.current_selection(source, receipt["importRoot"], receipt["namespace"])
        gen_uuid = store.begin_generation(source, args.generation_id, receipt, expected_digest)
        for i in range(0, len(normalized_decls), args.batch_size):
            batch_docs = normalized_decls[i : i + args.batch_size]
            rows = [
                (doc, term_map[doc["_key"]], module_ids[doc["module"]])
                for doc in batch_docs
            ]
            store.append_declarations(gen_uuid, rows)
        for i in range(0, len(normalized_edges), args.batch_size):
            store.append_dependencies(gen_uuid, normalized_edges[i : i + args.batch_size])
        new_sel = store.complete_and_select(gen_uuid, prior_sel, reconcile_public=True)
        report = {
            "status": "promoted",
            "mode": "generation_pinned",
            "generation_id": args.generation_id,
            "generation_uuid": str(gen_uuid),
            "source_id": str(dep_uuid),
            "arango_database": source.arango_database,
            "expected_decl_count": len(normalized_decls),
            "loaded_decl_count": len(normalized_decls),
            "active_public_represented_term_count": len(normalized_decls),
            "expected_edge_count": len(normalized_edges),
            "loaded_edge_count": len(normalized_edges),
            "active_public_term_term_count": len(normalized_edges),
            "module_count": len(module_ids),
            "source_digest": expected_digest,
            "previous_generation_uuid": str(prior_sel.generation) if prior_sel.generation else None,
            "active_generation_uuid": str(new_sel.generation),
            "revision": new_sel.revision,
        }
        _write_report(args.report_json, report)
        print(json.dumps(report, sort_keys=True))
        return 0
    finally:
        conn.close()


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Bridge ArangoDB Lean decls -> Auto-Ontology term store"
    )
    ap.add_argument("--arango-db", default=ARANGO_DATABASE or "infogeometry",
                    help="Arango database to read (default: ARANGO_DATABASE)")
    ap.add_argument("--decl-collection",
                    help="Explicit declaration collection for a legacy additive import")
    ap.add_argument("--generation-id",
                    help="Select source collections from a complete Arango receipt")
    ap.add_argument("--legacy-additive", action="store_true",
                    help="Acknowledge writes to shared additive tables; reads are not generation-pinned")
    ap.add_argument("--pin-generation", action="store_true",
                    help="Write generation-pinned snapshot into ig_decl_projection and reconcile public tables")
    ap.add_argument("--deployment-uuid",
                    help="Explicit nonzero deployment UUID for ig_decl_projection snapshot mode")
    ap.add_argument("--dry-run", action="store_true",
                    help="Validate source and compute digest without opening a PostgreSQL write connection")
    ap.add_argument("--decls-jsonl",
                    help="Offline declarations JSONL input path for --dry-run validation")
    ap.add_argument("--edges-jsonl",
                    help="Optional offline edges JSONL input path for --dry-run validation")
    ap.add_argument("--report-json", "--reconciliation-out", dest="report_json",
                    help="Optional file path to write JSON reconciliation/dry-run report")
    ap.add_argument("--batch-size", type=int, default=5000)
    ap.add_argument("--limit", type=int, default=0,
                    help="Max declarations (0 = all)")
    args = ap.parse_args()

    if args.decls_jsonl:
        if not args.dry_run:
            ap.error("--decls-jsonl offline input requires --dry-run")
        return _run_offline_jsonl_dry_run(args)

    pinned_mode = bool(args.pin_generation or args.deployment_uuid)
    if (args.generation_id is not None
            and not args.legacy_additive
            and not pinned_mode
            and not args.dry_run):
        ap.error(
            "--generation-id only selects Arango input unless --pin-generation / --deployment-uuid "
            "or --dry-run is set; PostgreSQL writes are legacy/additive. Pass --legacy-additive to "
            "acknowledge this. Generation-pinned projection is not implemented without --pin-generation "
            "or --deployment-uuid."
        )
    if args.generation_id is not None and args.limit != 0:
        ap.error("--generation-id requires --limit 0 to validate all source declarations")
    if args.generation_id is not None:
        try:
            validate_generation_id(args.generation_id)
        except ValueError as exc:
            ap.error(f"--generation-id: {exc}")
    if (args.generation_id is not None) == (args.decl_collection is not None):
        ap.error("provide exactly one of --generation-id or explicit --decl-collection")

    db = connect_arango(args.arango_db)
    if args.generation_id is not None:
        try:
            generation = resolve_decl_graph_generation(db, args.generation_id)
        except ValueError as exc:
            raise SystemExit(str(exc)) from exc
        decl_collection = generation["declCollection"]
    else:
        generation = None
        decl_collection = args.decl_collection
    if not decl_collection.replace("_", "").isalnum():
        raise SystemExit(f"unsafe declaration collection name: {decl_collection!r}")
    decls = db.collection(decl_collection)
    total = decls.count()
    print(f"ArangoDB {args.arango_db}: decls collection has {total} documents")
    if total == 0:
        raise SystemExit(f"refusing empty declaration import from {decl_collection!r}")

    # Validate the complete source before opening a PostgreSQL write transaction.
    invalid = list(db.aql.execute(
        "FOR d IN @@decls FILTER !IS_STRING(d.name) OR d.name == '' "
        "OR !IS_STRING(d._key) OR d._key == '' LIMIT 1 RETURN d._key",
        bind_vars={"@decls": decl_collection},
    ))
    if invalid:
        raise SystemExit("declaration source contains a missing name or identity")
    duplicate = list(db.aql.execute(
        "FOR d IN @@decls COLLECT name = d.name WITH COUNT INTO n "
        "FILTER n > 1 LIMIT 1 RETURN name",
        bind_vars={"@decls": decl_collection},
    ))
    if duplicate:
        raise SystemExit("declaration source contains duplicate names")

    if pinned_mode and generation is not None:
        return _run_pinned_generation_projection(args, db, generation, decl_collection, total)

    if args.dry_run:
        report = {
            "status": "dry_run_ok",
            "mode": "arango_preflight",
            "generation_id": args.generation_id,
            "decl_collection": decl_collection,
            "expected_decl_count": total,
            "loaded_decl_count": 0,
        }
        _write_report(args.report_json, report)
        print(json.dumps(report, sort_keys=True))
        return 0

    conn = psycopg.connect(**get_pg_connect())
    conn.autocommit = False
    cur = conn.cursor()

    db_id = ensure_catalog(cur, args.arango_db)
    schema_id = ensure_schema(cur, db_id)

    module_ids: dict[str, str] = {}
    imported = 0
    skipped_empty_name = 0

    aql = f"FOR d IN {decl_collection} SORT d.name "
    if args.limit > 0:
        aql += "LIMIT @limit "
    aql += (
        "RETURN { "
        "  _key: d._key, name: d.name, kind: d.kind, doc: d.doc, "
        "  module: d.module, relFile: d.relFile, line: d.line "
        "}"
    )

    cursor = db.aql.execute(
        aql,
        bind_vars={"limit": args.limit} if args.limit > 0 else None,
        batch_size=args.batch_size,
    )

    pending_modules: set[str] = set()
    pending_terms: list[dict] = []

    for doc in cursor:
        name = doc.get("name") or ""
        if not name:
            skipped_empty_name += 1
            continue
        module = doc.get("module") or "Unknown"
        pending_modules.add(module)
        rel_file = doc.get("relFile") or ""
        line = doc.get("line") or 0
        desc = (doc.get("doc") or "")
        if rel_file:
            desc += f"\n\nSource: {rel_file}:{line}"
        pending_terms.append({
            "name": name,
            "description": desc,
            "synonyms": [doc.get("kind") or ""],
            "aokey": doc.get("_key") or doc.get("key") or "",
            "module": module,
        })

        if len(pending_terms) >= args.batch_size:
            mod_map = upsert_modules(cur, schema_id, sorted(pending_modules))
            module_ids.update(mod_map)
            term_map = copy_terms(cur, pending_terms)
            links = []
            for t in pending_terms:
                links.append((module_ids[t["module"]], term_map[t["aokey"]]))
            link_table_terms(cur, links)
            imported += len(pending_terms)
            print(f"  imported {imported} terms... (modules: {len(module_ids)})")
            pending_modules.clear()
            pending_terms.clear()

    if pending_terms:
        mod_map = upsert_modules(cur, schema_id, sorted(pending_modules))
        module_ids.update(mod_map)
        term_map = copy_terms(cur, pending_terms)
        links = []
        for t in pending_terms:
            links.append((module_ids[t["module"]], term_map[t["aokey"]]))
        link_table_terms(cur, links)
        imported += len(pending_terms)

    if imported == 0:
        conn.rollback()
        cur.close()
        conn.close()
        raise SystemExit("no terms imported; refusing to report a successful empty ontology refresh")
    if args.generation_id is not None and (skipped_empty_name or imported != total):
        conn.rollback()
        cur.close()
        conn.close()
        raise SystemExit(
            f"incomplete generation projection: imported={imported}, expected={total}, "
            f"skipped={skipped_empty_name}"
        )
    conn.commit()
    cur.close()
    conn.close()
    report = {
        "status": "legacy_additive_committed",
        "mode": "legacy_additive",
        "generation_id": args.generation_id,
        "decl_collection": decl_collection,
        "expected_decl_count": total,
        "loaded_decl_count": imported,
        "module_count": len(module_ids),
    }
    _write_report(args.report_json, report)
    print(f"\nDone. Imported {imported} terms across {len(module_ids)} modules "
          f"into Auto-Ontology Postgres (output_mode=legacy_additive, "
          f"input_generation={args.generation_id or 'explicit_collection'}). "
          f"This does not publish a generation-pinned snapshot. "
          f"Skipped {skipped_empty_name} docs with no name.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
