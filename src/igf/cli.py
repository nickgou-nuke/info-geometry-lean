#!/usr/bin/env python3
"""Canonical igf CLI package entrypoint."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from igf.artifacts.compatibility_adapters import normalize_artifacts


def _add_build_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--nodes", default="artifacts/dag/index/decls.jsonl")
    parser.add_argument("--edges", default="artifacts/dag/index/edges.jsonl")
    parser.add_argument("--fingerprints", default="artifacts/dag/index/expr_fingerprints.jsonl")
    parser.add_argument("--output-dir", default="artifacts/dag/index")
    parser.add_argument("--run-id", default="")
    parser.add_argument("--ego-limit", type=int, default=40)
    parser.add_argument("--ego-radius", type=int, default=2)
    parser.add_argument("--min-scc-size", type=int, default=2)
    parser.add_argument("--binder-min-size", type=int, default=3)
    parser.add_argument("--max-patch-nodes", type=int, default=128)
    parser.add_argument("--spectral-k", type=int, default=8)
    parser.add_argument("--print-json", action="store_true")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="igf")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("preflight").add_argument("--print-json", action="store_true")

    build = sub.add_parser("build")
    _add_build_args(build)

    run = sub.add_parser("run")
    _add_build_args(run)
    run.add_argument("--schemas-dir", default="schemas")
    run.add_argument("--strict", action="store_true")
    run.add_argument("--ingest", action="store_true")
    run.add_argument("--verify", action="store_true")
    run.add_argument("--verify-limit", type=int, default=25)

    validate = sub.add_parser("validate")
    validate.add_argument("--dir", default="artifacts/dag/index")
    validate.add_argument("--schemas-dir", default="schemas")
    validate.add_argument("--strict", action="store_true")
    validate.add_argument("--max-errors", type=int, default=200)
    validate.add_argument("--print-json", action="store_true")

    normalize = sub.add_parser("normalize")
    normalize.add_argument("--input-dir", default="artifacts/dag/index")
    normalize.add_argument("--output-dir", default="artifacts/dag/index.normalized")
    normalize.add_argument("--print-json", action="store_true")

    ingest = sub.add_parser("ingest")
    ingest.add_argument("--dir", default="artifacts/dag/index")
    ingest.add_argument("--print-json", action="store_true")

    verify = sub.add_parser("verify")
    verify.add_argument("--run-id", default="")
    verify.add_argument("--limit", type=int, default=25)
    verify.add_argument("--print-json", action="store_true")

    maxent = sub.add_parser("maxent-candidates")
    maxent.add_argument("--run-id", default="")
    maxent.add_argument("--limit", type=int, default=25)
    maxent.add_argument("--min-abs-chiral-bias", type=float, default=0.5)
    maxent.add_argument("--print-json", action="store_true")

    barrier = sub.add_parser("barrier-candidates")
    barrier.add_argument("--run-id", default="")
    barrier.add_argument("--limit", type=int, default=25)
    barrier.add_argument("--min-abs-chiral-bias", type=float, default=0.5)
    barrier.add_argument("--barrier-weight", type=float, default=1.0)
    barrier.add_argument("--nullity-weight", type=float, default=1.0)
    barrier.add_argument("--print-json", action="store_true")

    report = sub.add_parser("report")
    report.add_argument("--dir", default="artifacts/dag/index")
    report.add_argument("--print-json", action="store_true")

    compact = sub.add_parser("compact")
    compact.add_argument("--max-files", type=int, default=50, help="Max files to process in this pass")
    compact.add_argument("--dry-run", action="store_true", help="Simulate without applying edits")

    cpg_dedup = sub.add_parser("cpg-dedup")
    cpg_dedup.add_argument("--out", default="reports/cpg_dedup_report.json")

    args = parser.parse_args(argv)

    if args.command == "preflight":
        from igf.config.preflight import print_preflight_json

        return print_preflight_json()

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

    if args.command == "maxent-candidates":
        from igf.config.loader import load_arango_config
        from igf.graph.arango_client import connect_db
        from igf.pipeline.candidates import find_maxent_style_patch_candidates

        cfg = load_arango_config()
        db = connect_db(cfg)
        result = find_maxent_style_patch_candidates(
            db,
            args.run_id or None,
            limit=int(args.limit),
            min_abs_chiral_bias=float(args.min_abs_chiral_bias),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1

    if args.command == "barrier-candidates":
        from igf.config.loader import load_arango_config
        from igf.graph.arango_client import connect_db
        from igf.pipeline.candidates import find_log_barrier_patch_candidates

        cfg = load_arango_config()
        db = connect_db(cfg)
        result = find_log_barrier_patch_candidates(
            db,
            args.run_id or None,
            limit=int(args.limit),
            min_abs_chiral_bias=float(args.min_abs_chiral_bias),
            barrier_weight=float(args.barrier_weight),
            nullity_weight=float(args.nullity_weight),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1

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
            ego_limit=int(args.ego_limit),
            ego_radius=int(args.ego_radius),
            min_scc_size=int(args.min_scc_size),
            binder_min_size=int(args.binder_min_size),
            max_patch_nodes=int(args.max_patch_nodes),
            spectral_k=int(args.spectral_k),
            do_ingest=bool(args.ingest or args.verify),
            do_verify=bool(args.verify),
            verify_limit=int(args.verify_limit),
        )
        print(json.dumps(result, ensure_ascii=False))
        return int(result.get("exit_code", 1 if not result.get("ok") else 0))

    if args.command == "compact":
        from igf.cpg.self_compact import LosslessSelfCompactor

        compactor = LosslessSelfCompactor()
        summary = compactor.run_compactification_pass(max_files=args.max_files)
        return 0 if summary.get("rolled_back", 0) == 0 else 1

    if args.command == "cpg-dedup":
        from igf.cpg.dedup import ArangoCPGDeduplicator

        dedup = ArangoCPGDeduplicator()
        manifest = dedup.generate_deduplication_manifest(out_path=Path(args.out))
        return 0 if manifest else 1

    return 1


if __name__ == "__main__":
    sys.exit(main())
