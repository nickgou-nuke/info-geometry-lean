#!/usr/bin/env python3
"""Import extracted Lean 4 tactic states into ArangoDB.

Schema:
  vertices: tactic_states, lean_decls
  edges:    has_tactic_state

Default mode is a dry run: it validates input and reports graph sizes without
requiring ArangoDB or python-arango.  Use `--execute` to write to ArangoDB.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any


def fail(message: str) -> None:
    raise SystemExit(f"ingest_tactics_arango: {message}")


try:
    from proofs.tools.confabulation_monitor import validate_arango, scan_proofs, summarize_proofs
except Exception:  # pragma: no cover - optional dependency guard
    validate_arango = None  # type: ignore[misc,assignment]
    scan_proofs = None  # type: ignore[misc,assignment]
    summarize_proofs = None  # type: ignore[misc,assignment]


def load_env_file(path: Path | None) -> None:
    if path is None or not path.exists():
        return
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :].strip()
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


def load_default_arango_env(explicit: Path | None) -> None:
    candidates = []
    if explicit is not None:
        candidates.append(explicit)
    for name in ("ARANGO_ENV_FILE", "HIVE_ARANGO_ENV_FILE"):
        value = os.environ.get(name)
        if value:
            candidates.append(Path(value))
    candidates.extend([
        Path("/home/goutev/.config/arango/env.sh"),
        Path(__file__).resolve().parent / "env.sh",
        Path("/home/goutev/auto/configs/local/hive_arango.env"),
    ])
    for candidate in candidates:
        load_env_file(candidate)
    if "ARANGO_PASSWORD" not in os.environ and "ARANGO_PASS" in os.environ:
        os.environ["ARANGO_PASSWORD"] = os.environ["ARANGO_PASS"]
    if "ARANGO_PASS" not in os.environ and "ARANGO_PASSWORD" in os.environ:
        os.environ["ARANGO_PASS"] = os.environ["ARANGO_PASSWORD"]
    if "ARANGO_USER" not in os.environ and "ARANGO_USERNAME" in os.environ:
        os.environ["ARANGO_USER"] = os.environ["ARANGO_USERNAME"]
    if "ARANGO_USERNAME" not in os.environ and "ARANGO_USER" in os.environ:
        os.environ["ARANGO_USERNAME"] = os.environ["ARANGO_USER"]
    if "ARANGO_HOST" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_HOST"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_URL" not in os.environ and "ARANGO_ENDPOINT" in os.environ:
        os.environ["ARANGO_URL"] = os.environ["ARANGO_ENDPOINT"]
    if "ARANGO_DB" not in os.environ and "ARANGO_DATABASE" in os.environ:
        os.environ["ARANGO_DB"] = os.environ["ARANGO_DATABASE"]


def stable_key(*parts: str) -> str:
    raw = "\x1f".join(parts)
    digest = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:16]
    safe = "_".join(parts[:2])
    safe = "".join(ch if (ch.isascii() and ch.isalnum()) or ch in "_-" else "_" for ch in safe)
    safe = safe.strip("_")[:180]
    return f"{safe}_{digest}" if safe else digest


def decl_key(name: str) -> str:
    safe = name.replace(".", "_").replace("`", "_").replace("«", "").replace("»", "")
    result: list[str] = []
    for ch in safe:
        if ch.isascii() and (ch.isalnum() or ch in "_:-"):
            result.append(ch)
        else:
            result.append("_")
    return "".join(result).strip("_")[:200]


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                fail(f"{path}:{line_number}: invalid JSONL: {exc}")
            records.append(record)
    if not records:
        fail(f"{path}: no records")
    return records


def setup_arango(args: argparse.Namespace):
    try:
        from arango import ArangoClient  # type: ignore
    except ImportError as exc:
        fail("python-arango is required for --execute; install with `pip install python-arango`")
        raise exc

    client = ArangoClient(hosts=args.host)
    sys_db = client.db("_system", username=args.user, password=args.password)
    if not sys_db.has_database(args.database):
        sys_db.create_database(args.database)
    db = client.db(args.database, username=args.user, password=args.password)

    for collection in ["lean_decls", "tactic_states"]:
        if not db.has_collection(collection):
            db.create_collection(collection)

    if not db.has_graph(args.graph):
        graph = db.create_graph(args.graph)
    else:
        graph = db.graph(args.graph)

    if not graph.has_edge_definition("has_tactic_state"):
        graph.create_edge_definition(
            edge_collection="has_tactic_state",
            from_vertex_collections=["lean_decls"],
            to_vertex_collections=["tactic_states"],
        )
    return db, graph


def import_records(records: list[dict[str, Any]], args: argparse.Namespace) -> dict[str, int]:
    counts = {
        "tactic_records": len(records),
        "lean_decls": 0,
        "tactic_states": 0,
        "has_tactic_state": 0,
    }

    if args.execute:
        db, graph = setup_arango(args)
        lean_decls = db.collection("lean_decls")
        tactic_states = db.collection("tactic_states")
        has_tactic_state = graph.edge_collection("has_tactic_state")
    else:
        lean_decls = tactic_states = has_tactic_state = None

    batch_decls = []
    batch_tactics = []
    batch_edges = []
    seen_decls = set()
    BATCH_SIZE = 5000

    def flush_batches():
        if not args.execute:
            return
        if batch_decls:
            lean_decls.insert_many(batch_decls, overwrite=False, silent=True)
            batch_decls.clear()
        if batch_tactics:
            tactic_states.insert_many(batch_tactics, overwrite=True, silent=True)
            batch_tactics.clear()
        if batch_edges:
            has_tactic_state.insert_many(batch_edges, overwrite=False, silent=True)
            batch_edges.clear()

    for idx, record in enumerate(records):
        theorem_name = record.get("theorem", "unknown")
        de_bruijn_hash = record.get("de_bruijn_hash", "")
        file_path = record.get("file", "")
        tactic = record.get("tactic", "")
        goals_before = record.get("goals_before", [])
        goals_after = record.get("goals_after", [])

        source_key = decl_key(theorem_name)
        tactic_key = stable_key("tactic", theorem_name, str(idx), de_bruijn_hash)

        # 1. Prepare theorem declaration
        if source_key not in seen_decls:
            seen_decls.add(source_key)
            batch_decls.append({
                "_key": source_key,
                "name": theorem_name,
                "module": theorem_name.split(".")[0],
            })
            counts["lean_decls"] += 1

        # 2. Prepare Tactic State node
        batch_tactics.append({
            "_key": tactic_key,
            "theorem": theorem_name,
            "de_bruijn_hash": de_bruijn_hash,
            "file": file_path,
            "tactic": tactic,
            "goals_before": goals_before,
            "goals_after": goals_after,
            "sequence_index": idx
        })
        counts["tactic_states"] += 1

        # 3. Prepare Edge
        batch_edges.append({
            "_key": stable_key("has_tactic", source_key, tactic_key),
            "_from": f"lean_decls/{source_key}",
            "_to": f"tactic_states/{tactic_key}",
        })
        counts["has_tactic_state"] += 1

        if len(batch_tactics) >= BATCH_SIZE:
            flush_batches()

    flush_batches()
    return counts


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tactic_jsonl", type=Path, help="tactic_states.jsonl file produced by ExtractInfoTree.lean")
    parser.add_argument("--execute", action="store_true", help="write to ArangoDB; default is dry-run")
    parser.add_argument("--env-file", type=Path, default=None, help="optional shell env file with ARANGO_* settings")
    parser.add_argument("--host", default=None)
    parser.add_argument("--user", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--graph", default=None)

    monitor = parser.add_argument_group("confabulation monitor")
    monitor.add_argument("--monitor", action="store_true", help="Run post-ingestion confabulation checks")
    monitor.add_argument("--monitor-scan-root", type=Path, default=Path("proofs"), help="Root Lean tree for vacuity scan")
    monitor.add_argument("--monitor-out", type=Path, default=Path("proofs/tools/out/monitor"), help="Monitor report directory")
    args = parser.parse_args()
    
    load_default_arango_env(args.env_file)
    if args.host is None:
        args.host = os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or os.getenv("ARANGO_HOST") or "http://localhost:8529"
    if args.user is None:
        args.user = os.getenv("ARANGO_USERNAME") or os.getenv("ARANGO_USER") or "root"
    if args.password is None:
        args.password = os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS") or "password"
    if args.database is None:
        args.database = os.getenv("ARANGO_DATABASE") or os.getenv("ARANGO_DB") or "info_geometry"
    if args.graph is None:
        args.graph = os.getenv("ARANGO_GRAPH") or "LeanUniverseGraph"

    records = load_jsonl(args.tactic_jsonl)
    counts = import_records(records, args)
    
    mode = "executed" if args.execute else "dry-run"
    print(f"{mode}: " + " ".join(f"{key}={value}" for key, value in counts.items()), file=sys.stderr)

    if args.monitor:
        print("monitor: running post-ingestion confabulation checks", file=sys.stderr)
        arango_report = None
        if validate_arango is not None:
            try:
                arango_report = validate_arango(args.host, args.database, args.user, args.password)
                print(f"monitor: arango validate={json.dumps(arango_report, ensure_ascii=True)}", file=sys.stderr)
            except Exception as exc:  # pragma: no cover - runtime guard
                print(f"monitor: arango validate failed: {exc}", file=sys.stderr)
                arango_report = {"error": str(exc)}
        else:
            print("monitor: arango validation skipped; confabulation_monitor not importable", file=sys.stderr)

        vac_report = None
        if scan_proofs is not None and summarize_proofs is not None:
            try:
                root = args.monitor_scan_root.resolve()
                claims, vacuities = [], []
                for lean_file in sorted(root.glob("**/*.lean")):
                    claims.extend([])
                    vacuities.extend(scan_proofs(lean_file))
                vac_report = summarize_proofs(vacuities)
                print(f"monitor: proof vancies={json.dumps(vac_report, ensure_ascii=True)}", file=sys.stderr)
            except Exception as exc:  # pragma: no cover - runtime guard
                print(f"monitor: proof scan failed: {exc}", file=sys.stderr)
                vac_report = {"error": str(exc)}
        else:
            print("monitor: proof scan skipped; confabulation_monitor not importable", file=sys.stderr)

        report = {
            "monitor": {
                "database": args.database,
                "graph": args.graph,
                "counts": counts,
                "arango": arango_report,
                "proofs": vac_report,
            }
        }
        out_dir = args.monitor_out.resolve()
        out_dir.mkdir(parents=True, exist_ok=True)
        out_file = out_dir / "ingest_monitor.json"
        out_file.write_text(json.dumps(report, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
        print(f"monitor: wrote {out_file}")


if __name__ == "__main__":
    main()
