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

from igf.config.preflight import print_preflight_json
from igf.pipeline.validate import validate_artifacts


def cmd_not_implemented(name: str) -> int:
    print(json.dumps({"ok": False, "command": name, "status": "not_implemented"}))
    return 1


def main() -> int:
    p = argparse.ArgumentParser(prog="igf")
    sub = p.add_subparsers(dest="command", required=True)

    sub.add_parser("preflight").add_argument("--print-json", action="store_true")

    for name in ["build", "ingest", "verify", "report", "run"]:
        sp = sub.add_parser(name)
        sp.add_argument("--print-json", action="store_true")

    v = sub.add_parser("validate")
    v.add_argument("--dir", default="artifacts/dag/index")
    v.add_argument("--schemas-dir", default="schemas")
    v.add_argument("--strict", action="store_true")
    v.add_argument("--max-errors", type=int, default=200)
    v.add_argument("--print-json", action="store_true")

    args = p.parse_args()

    if args.command == "preflight":
        return print_preflight_json()
    if args.command == "validate":
        result = validate_artifacts(
            Path(args.dir),
            Path(args.schemas_dir),
            strict=bool(args.strict),
            max_errors=int(args.max_errors),
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if result.get("ok") else 1
    if args.command == "build":
        return cmd_not_implemented("build")
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
