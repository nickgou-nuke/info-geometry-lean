#!/usr/bin/env python3
"""
Bridge: ArangoDB (info-geometry-lean declaration graph) -> Auto-Ontology Postgres ontology store.

Reads Lean declarations from the ArangoDB ``decls`` collection and writes them
as Auto-Ontology ``term`` rows, grouped by Lean module into ``catalog_table``
rows linked via ``table__term`` edges.

Idempotent: re-running upserts shared legacy terms without duplicating them
(terms keyed by Arango ``_key`` via ``imported_id`` + name/source unique constraint).

Uses psycopg3 ``cursor.copy()`` (COPY protocol) for bulk inserts, since psycopg3
removed ``execute_values``.

Run from the repository root with the configured Arango and populated
Auto-Ontology PostgreSQL environment loaded without printing credentials.
See docs/AUTO_ONTOLOGY_AGENT_OPERATIONS.md for deployment selection and
docs/ASTAQLHASH-HOWTO.md for complete-generation verification.

Usage (generation mode selects Arango input and writes legacy additive tables):
    python3 tools/infra/arango_to_ontology.py \
        --arango-db infogeometry --generation-id "$GENERATION_ID" --legacy-additive
"""
from __future__ import annotations

import argparse
import csv
import io
import os
import sys
from datetime import datetime, timezone

import psycopg
from arango import ArangoClient
from decl_graph_generation import resolve_decl_graph_generation, validate_generation_id


ARANGO_ENDPOINT = os.environ["ARANGO_ENDPOINT"]
ARANGO_DATABASE = os.environ["ARANGO_DATABASE"]
ARANGO_USER = os.environ["ARANGO_USER"]
ARANGO_PASS = os.environ["ARANGO_PASS"]

PG_CONNECT = {
    "user": os.environ["POSTGRES_USER"],
    "password": os.environ["POSTGRES_PASSWORD"],
    "host": os.environ.get("POSTGRES_HOST", "localhost"),
    "port": os.environ.get("POSTGRES_PORT", "5433"),
    "dbname": os.environ.get("POSTGRES_DATABASE", "auto_ontology"),
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def connect_arango(database: str):
    client = ArangoClient(hosts=ARANGO_ENDPOINT)
    return client.db(
        database, username=ARANGO_USER, password=ARANGO_PASS, verify=True
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
    # Individual upserts (modules are few).
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
    # Staging table.
    cur.execute("DROP TABLE IF EXISTS pg_temp.term_staging")
    cur.execute(
        "CREATE TEMP TABLE term_staging (LIKE term INCLUDING DEFAULTS) ON COMMIT DROP"
    )
    # COPY rows in.
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
    # Insert from staging into term with ON CONFLICT.
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


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Bridge ArangoDB Lean decls -> Auto-Ontology term store"
    )
    ap.add_argument("--arango-db", default=ARANGO_DATABASE,
                    help="Arango database to read (default: ARANGO_DATABASE)")
    ap.add_argument("--decl-collection",
                    help="Explicit declaration collection for a legacy additive import")
    ap.add_argument("--generation-id",
                    help="Select source collections from a complete Arango receipt; this does not create a PostgreSQL snapshot")
    ap.add_argument("--legacy-additive", action="store_true",
                    help="Acknowledge writes to shared additive tables; reads are not generation-pinned")
    ap.add_argument("--batch-size", type=int, default=5000)
    ap.add_argument("--limit", type=int, default=0,
                    help="Max declarations (0 = all)")
    args = ap.parse_args()

    if args.generation_id is not None and not args.legacy_additive:
        ap.error("--generation-id only selects Arango input; PostgreSQL writes are legacy/additive. Pass --legacy-additive to acknowledge this. Generation-pinned projection is not implemented.")
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

    conn = psycopg.connect(**PG_CONNECT)
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
    pending_links: list[tuple[str, str]] = []

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
    # Publish the complete projection atomically. In particular, do not commit
    # batches before checking that the generation stream was fully consumed.
    conn.commit()
    cur.close()
    conn.close()
    print(f"\nDone. Imported {imported} terms across {len(module_ids)} modules "
          f"into Auto-Ontology Postgres (output_mode=legacy_additive, "
          f"input_generation={args.generation_id or 'explicit_collection'}). "
          f"This does not publish a generation-pinned snapshot. "
          f"Skipped {skipped_empty_name} docs with no name.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
