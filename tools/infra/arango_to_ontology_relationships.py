#!/usr/bin/env python3
"""
Bridge part 2: ArangoDB edges -> Auto-Ontology term__term relationships.

Reads Lean declaration->declaration edges from ArangoDB ``edges`` collection
(src/dst names + kind) and writes them as Auto-Ontology ``term__term``
association rows, linking two ``term`` rows by their ``imported_id`` (Arango
``_key`` of the source decl) and matched ``dst`` name.
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
    endpoint = os.environ.get("ARANGO_ENDPOINT") or ARANGO_ENDPOINT
    database = database_override or os.environ.get("ARANGO_DATABASE") or ARANGO_DATABASE
    user = os.environ.get("ARANGO_USER") or ARANGO_USER
    password = os.environ.get("ARANGO_PASS") or ARANGO_PASS
    if not (endpoint and database and user and password):
        try:
            from arango_env import (
                arango_database,
                arango_endpoint,
                arango_password,
                arango_username,
                load_repo_arango_env,
            )
            load_repo_arango_env()
            endpoint = endpoint or arango_endpoint()
            database = database or arango_database()
            user = user or arango_username()
            password = password or arango_password()
        except Exception:
            pass
    return endpoint, database or "infogeometry", user, password


def get_pg_connect() -> dict[str, str]:
    PG_CONNECT["user"] = os.environ.get("POSTGRES_USER", PG_CONNECT.get("user", ""))
    PG_CONNECT["password"] = os.environ.get("POSTGRES_PASSWORD", PG_CONNECT.get("password", ""))
    PG_CONNECT["host"] = os.environ.get("POSTGRES_HOST", PG_CONNECT.get("host", "localhost"))
    PG_CONNECT["port"] = os.environ.get("POSTGRES_PORT", PG_CONNECT.get("port", "5433"))
    PG_CONNECT["dbname"] = os.environ.get("POSTGRES_DATABASE", PG_CONNECT.get("dbname", "auto_ontology"))
    return PG_CONNECT


def connect_arango(database: str):
    endpoint, db_name, user, password = _resolve_arango_env(database)
    client = ArangoClient(hosts=endpoint)
    return client.db(
        db_name, username=user, password=password, verify=True
    )


def ensure_term_term_table(cur):
    """Create the term__term association table if it does not exist."""
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


def load_term_ids(cur, name_to_key: dict[str, str]) -> dict[str, str]:
    """Resolve imported identities without silently collapsing duplicate rows."""
    cur.execute("SELECT id, imported_id, name, source FROM term WHERE imported_id IS NOT NULL")
    expected_names = {key: name for name, key in name_to_key.items()}
    result: dict[str, str] = {}
    for tid, imp_id, name, source in cur.fetchall():
        if imp_id in result:
            raise ValueError(f"ambiguous imported term identity {imp_id!r}")
        if imp_id in expected_names and (name != expected_names[imp_id] or source != "semantic"):
            raise ValueError(f"imported term identity {imp_id!r} has inconsistent name/source")
        result[imp_id] = tid
    return result


def load_decl_keys(db, decl_collection: str) -> dict[str, str]:
    """Map declaration FQNs to stable Arango keys in the selected snapshot."""
    if not decl_collection.replace("_", "").isalnum():
        raise SystemExit(f"unsafe declaration collection name: {decl_collection!r}")
    cursor = db.aql.execute(
        f"FOR d IN {decl_collection} "
        "RETURN {name: d.name, key: d._key}"
    )
    result: dict[str, str] = {}
    for row in cursor:
        if (not isinstance(row.get("name"), str) or not row["name"]
                or not isinstance(row.get("key"), str) or not row["key"]):
            raise ValueError(f"missing declaration name or identity in {decl_collection!r}")
        if row["name"] in result:
            raise ValueError(f"duplicate declaration name {row['name']!r} in {decl_collection!r}")
        result[row["name"]] = row["key"]
    return result


def require_generation_terms(name_to_key: dict[str, str], key_to_term: dict[str, str]) -> None:
    """Require the complete term projection before writing generation edges."""
    missing = sorted(name for name, key in name_to_key.items() if key not in key_to_term)
    if missing:
        raise ValueError(
            f"generation has {len(missing)} declarations without imported terms; "
            f"run its term importer first (examples: {', '.join(missing[:5])})"
        )


def copy_relationships(cur, pairs: list[tuple[str, str, str]]) -> None:
    """Bulk upsert term__term rows via a temp staging table + COPY."""
    if not pairs:
        return
    cur.execute("DROP TABLE IF EXISTS pg_temp.rel_staging")
    cur.execute(
        "CREATE TEMP TABLE rel_staging (src_term_id text, dst_term_id text, kind text) "
        "ON COMMIT DROP"
    )
    buf = io.StringIO()
    writer = csv.writer(buf)
    for src_id, dst_id, kind in pairs:
        writer.writerow([src_id, dst_id, kind])
    buf.seek(0)
    with cur.copy(
        "COPY rel_staging (src_term_id, dst_term_id, kind) FROM STDIN WITH (FORMAT csv)"
    ) as copy:
        copy.write(buf.read())
    cur.execute(
        "INSERT INTO term__term (src_term_id, dst_term_id, kind, created_at) "
        "SELECT src_term_id, dst_term_id, kind, now() FROM rel_staging "
        "ON CONFLICT (src_term_id, dst_term_id, kind) DO NOTHING"
    )


def validate_dependency_edges(db, edge_collection: str, decl_collection: str) -> None:
    """Reject untyped, mis-keyed, foreign, or dangling edges before PG writes."""
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


def _write_report(report_path: str | None, payload: dict) -> None:
    if report_path:
        out = Path(report_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Bridge ArangoDB edges -> Auto-Ontology term__term relationships"
    )
    ap.add_argument("--arango-db", default=ARANGO_DATABASE or "infogeometry",
                    help="Arango database to read (default: ARANGO_DATABASE)")
    ap.add_argument("--edge-collection",
                    help="Explicit edge collection for a legacy additive import")
    ap.add_argument("--decl-collection",
                    help="Matching declaration collection for a legacy additive import")
    ap.add_argument("--generation-id",
                    help="Select source collections from a complete Arango receipt")
    ap.add_argument("--legacy-additive", action="store_true",
                    help="Acknowledge writes to shared additive tables; reads are not generation-pinned")
    ap.add_argument("--dry-run", action="store_true",
                    help="Validate edge integrity without opening a PostgreSQL write connection")
    ap.add_argument("--decls-jsonl",
                    help="Offline declarations JSONL input path for --dry-run validation")
    ap.add_argument("--edges-jsonl",
                    help="Offline edges JSONL input path for --dry-run validation")
    ap.add_argument("--report-json", "--reconciliation-out", dest="report_json",
                    help="Optional file path to write JSON reconciliation/dry-run report")
    ap.add_argument("--batch-size", type=int, default=5000)
    ap.add_argument("--limit", type=int, default=0,
                    help="Max edges (0 = all)")
    args = ap.parse_args()

    if args.decls_jsonl or args.edges_jsonl:
        if not (args.dry_run and args.decls_jsonl and args.edges_jsonl):
            ap.error("offline relationship validation requires --dry-run, --decls-jsonl, and --edges-jsonl")
        from arango_to_ontology import _run_offline_jsonl_dry_run
        args.deployment_uuid = None
        return _run_offline_jsonl_dry_run(args)

    if args.generation_id is not None and not args.legacy_additive and not args.dry_run:
        ap.error(
            "--generation-id only selects Arango input; PostgreSQL writes are legacy/additive. "
            "Pass --legacy-additive to acknowledge this (or use arango_to_ontology.py --pin-generation). "
            "Generation-pinned projection is not implemented in standalone relationship mode."
        )
    if args.generation_id is not None and args.limit != 0:
        ap.error("--generation-id requires --limit 0 to validate all source edges")
    if args.generation_id is not None:
        try:
            validate_generation_id(args.generation_id)
        except ValueError as exc:
            ap.error(f"--generation-id: {exc}")
    if args.generation_id is not None and (args.edge_collection or args.decl_collection):
        ap.error("--generation-id cannot be combined with legacy collection names")
    if args.generation_id is None and not (args.edge_collection and args.decl_collection):
        ap.error("pass --generation-id or explicitly pass both --edge-collection and --decl-collection")
    db = connect_arango(args.arango_db)
    if args.generation_id is not None:
        try:
            generation = resolve_decl_graph_generation(db, args.generation_id)
        except ValueError as exc:
            raise SystemExit(str(exc)) from exc
        edge_collection = generation["edgeCollection"]
        decl_collection = generation["declCollection"]
    else:
        edge_collection = args.edge_collection
        decl_collection = args.decl_collection

    if not edge_collection.replace("_", "").isalnum():
        raise SystemExit(f"unsafe edge collection name: {edge_collection!r}")
    if not decl_collection.replace("_", "").isalnum():
        raise SystemExit(f"unsafe declaration collection name: {decl_collection!r}")
    edges_col = db.collection(edge_collection)
    total = edges_col.count()
    print(f"ArangoDB {args.arango_db}: edge collection {edge_collection!r} has {total} documents")
    if total == 0 and args.generation_id is None:
        raise SystemExit(f"refusing empty relationship import from {edge_collection!r}")

    validate_dependency_edges(db, edge_collection, decl_collection)

    if args.dry_run:
        name_to_decl_key = load_decl_keys(db, decl_collection)
        report = {
            "status": "dry_run_ok",
            "mode": "arango_relationships_preflight",
            "generation_id": args.generation_id,
            "decl_collection": decl_collection,
            "edge_collection": edge_collection,
            "expected_decl_count": len(name_to_decl_key),
            "expected_edge_count": total,
            "loaded_edge_count": 0,
        }
        _write_report(args.report_json, report)
        print(json.dumps(report, sort_keys=True))
        return 0

    conn = psycopg.connect(**get_pg_connect())
    conn.autocommit = False
    cur = conn.cursor()

    # Resolve term ids.
    name_to_decl_key = load_decl_keys(db, decl_collection)
    imported_id_to_term = load_term_ids(cur, name_to_decl_key)
    if args.generation_id:
        require_generation_terms(name_to_decl_key, imported_id_to_term)
    ensure_term_term_table(cur)
    print(f"Resolved {len(imported_id_to_term)} terms by imported_id and "
          f"{len(name_to_decl_key)} declarations from {decl_collection!r}")

    imported = 0
    skipped_no_src = 0
    skipped_no_dst = 0

    aql = f"FOR e IN {edge_collection} "
    if args.limit > 0:
        aql += "LIMIT @limit "
    aql += "SORT e._key RETURN { _key: e._key, src: e.src, dst: e.dst, kind: e.kind }"

    pending: list[tuple[str, str, str]] = []

    cursor = db.aql.execute(
        aql,
        bind_vars={"limit": args.limit} if args.limit > 0 else None,
        batch_size=args.batch_size,
    )

    for edge in cursor:
        src_name = edge.get("src") or ""
        dst_name = edge.get("dst") or ""
        kind = edge.get("kind") or "unknown"
        if not src_name or not dst_name:
            if not src_name:
                skipped_no_src += 1
            if not dst_name:
                skipped_no_dst += 1
            continue

        src_key = name_to_decl_key.get(src_name)
        dst_key = name_to_decl_key.get(dst_name)
        src_id = imported_id_to_term.get(src_key) if src_key else None
        dst_id = imported_id_to_term.get(dst_key) if dst_key else None

        if not src_id:
            skipped_no_src += 1
            continue
        if not dst_id:
            skipped_no_dst += 1
            continue
        pending.append((src_id, dst_id, kind))

        if len(pending) >= args.batch_size:
            copy_relationships(cur, pending)
            imported += len(pending)
            print(f"  imported {imported} relationships...")
            pending.clear()

    if pending:
        copy_relationships(cur, pending)
        imported += len(pending)

    if args.generation_id is not None and imported != total:
        conn.rollback()
        cur.close()
        conn.close()
        raise SystemExit(f"incomplete generation relationship import: processed {imported} of {total}")
    if imported == 0 and args.generation_id is None:
        conn.rollback()
        cur.close()
        conn.close()
        raise SystemExit("no relationships imported; declaration terms may be missing or from another generation")
    if skipped_no_src or skipped_no_dst:
        conn.rollback()
        cur.close()
        conn.close()
        raise SystemExit("incomplete relationship import: unresolved endpoints were skipped")
    conn.commit()
    cur.close()
    conn.close()
    report = {
        "status": "legacy_additive_committed",
        "mode": "legacy_additive",
        "generation_id": args.generation_id,
        "decl_collection": decl_collection,
        "edge_collection": edge_collection,
        "expected_edge_count": total,
        "loaded_edge_count": imported,
    }
    _write_report(args.report_json, report)
    print(f"\nDone. Imported {imported} relationships "
          f"(skipped {skipped_no_src} with no src term, "
          f"{skipped_no_dst} with no dst term; output_mode=legacy_additive, "
          f"input_generation={args.generation_id or 'explicit_collection'}). "
          f"This does not publish a generation-pinned snapshot.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
