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
        return cmd_not_implemented("ingest")
    if args.command == "verify":
        return cmd_not_implemented("verify")
    if args.command == "report":
        return cmd_not_implemented("report")
    if args.command == "run":
        return cmd_not_implemented("run")

    return 1


if __name__ == "__main__":
    sys.exit(main())
