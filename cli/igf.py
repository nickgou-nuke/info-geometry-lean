#!/usr/bin/env python3
"""Minimal igf CLI skeleton (greenfield bootstrap)."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from igf.artifacts.compatibility_adapters import normalize_artifacts


def cmd_not_implemented(name: str) -> int:
    print(json.dumps({"ok": False, "command": name, "status": "not_implemented"}))
    return 1


def main() -> int:
    p = argparse.ArgumentParser(prog="igf")
    sub = p.add_subparsers(dest="command", required=True)

    sub.add_parser("preflight").add_argument("--print-json", action="store_true")

    for name in ["ingest", "verify", "report", "run", "normalize"]:
        sp = sub.add_parser(name)
        sp.add_argument("--print-json", action="store_true")

    b = sub.add_parser("build")
    b.add_argument("--nodes", default="artifacts/leantrail/arango/ig_nodes.jsonl")
    b.add_argument("--edges", default="artifacts/leantrail/arango/ig_edges.jsonl")
    b.add_argument("--fingerprints", default="artifacts/dag/index/expr_fingerprints.jsonl")
    b.add_argument("--output-dir", default="artifacts/dag/index")
    b.add_argument("--run-id", default="")
    b.add_argument("--ego-limit", type=int, default=40)
    b.add_argument("--ego-radius", type=int, default=2)
    b.add_argument("--min-scc-size", type=int, default=2)
    b.add_argument("--binder-min-size", type=int, default=3)
    b.add_argument("--max-patch-nodes", type=int, default=128)
    b.add_argument("--spectral-k", type=int, default=8)
    b.add_argument("--print-json", action="store_true")

    n = sub.choices["normalize"]
    n.add_argument("--input-dir", default="artifacts/dag/index")
    n.add_argument("--output-dir", default="artifacts/dag/index.normalized")

    ingest = sub.choices["ingest"]
    ingest.add_argument("--dir", default="artifacts/dag/index")

    verify = sub.choices["verify"]
    verify.add_argument("--run-id", default="")
    verify.add_argument("--limit", type=int, default=25)

    report = sub.choices["report"]
    report.add_argument("--dir", default="artifacts/dag/index")

    run = sub.choices["run"]
    run.add_argument("--nodes", default="artifacts/leantrail/arango/ig_nodes.jsonl")
    run.add_argument("--edges", default="artifacts/leantrail/arango/ig_edges.jsonl")
    run.add_argument("--fingerprints", default="artifacts/dag/index/expr_fingerprints.jsonl")
    run.add_argument("--output-dir", default="artifacts/dag/index")
    run.add_argument("--schemas-dir", default="schemas")
    run.add_argument("--run-id", default="")
    run.add_argument("--strict", action="store_true")

    v = sub.add_parser("validate")
    v.add_argument("--dir", default="artifacts/dag/index")
    v.add_argument("--schemas-dir", default="schemas")
    v.add_argument("--strict", action="store_true")
    v.add_argument("--max-errors", type=int, default=200)
    v.add_argument("--print-json", action="store_true")

    args = p.parse_args()

    if args.command == "preflight":
        from igf.config.preflight import print_preflight_json

        return print_preflight_json()
    if args.command == "validate":
        from igf.pipeline.validate import validate_artifacts

        result = validate_artifacts(
            Path(args.dir),
            Path(args.schemas_dir),
            strict=bool(args.strict),
            max_errors=int(args.max_errors),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "build":
        from igf.pipeline.build import build_chiral_patches

        fingerprint_path = Path(args.fingerprints) if args.fingerprints else None
        if fingerprint_path is not None and not fingerprint_path.exists():
            fingerprint_path = None
        result = build_chiral_patches(
            nodes=Path(args.nodes),
            edges=Path(args.edges),
            fingerprints=fingerprint_path,
            output_dir=Path(args.output_dir),
            run_id=args.run_id or None,
            ego_limit=int(args.ego_limit),
            ego_radius=int(args.ego_radius),
            min_scc_size=int(args.min_scc_size),
            binder_min_size=int(args.binder_min_size),
            max_patch_nodes=int(args.max_patch_nodes),
            spectral_k=int(args.spectral_k),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "normalize":
        result = normalize_artifacts(Path(args.input_dir), Path(args.output_dir))
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "ingest":
        from igf.config.loader import load_arango_config
        from igf.graph.arango_client import connect_db
        from igf.pipeline.ingest import ingest_artifacts

        cfg = load_arango_config()
        db = connect_db(cfg)
        result = ingest_artifacts(db, Path(args.dir))
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "verify":
        from igf.config.loader import load_arango_config
        from igf.graph.arango_client import connect_db
        from igf.pipeline.verify import verify_run

        cfg = load_arango_config()
        db = connect_db(cfg)
        result = verify_run(db, args.run_id or None, limit=int(args.limit))
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 2
    if args.command == "report":
        from igf.pipeline.report import report_artifacts

        result = report_artifacts(Path(args.dir))
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "run":
        from igf.pipeline.orchestrator import run_offline_pipeline

        fingerprint_path = Path(args.fingerprints) if args.fingerprints else None
        if fingerprint_path is not None and not fingerprint_path.exists():
            fingerprint_path = None
        result = run_offline_pipeline(
            nodes=Path(args.nodes),
            edges=Path(args.edges),
            fingerprints=fingerprint_path,
            output_dir=Path(args.output_dir),
            schemas_dir=Path(args.schemas_dir),
            run_id=args.run_id or None,
            strict=bool(args.strict),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1

    return 1


if __name__ == "__main__":
    sys.exit(main())
