#!/usr/bin/env python3
"""Minimal igf CLI skeleton (greenfield bootstrap)."""

from __future__ import annotations

import argparse
import json
import sys


def cmd_not_implemented(name: str) -> int:
    print(json.dumps({"ok": False, "command": name, "status": "not_implemented"}))
    return 1


def main() -> int:
    p = argparse.ArgumentParser(prog="igf")
    sub = p.add_subparsers(dest="command", required=True)

    for name in ["preflight", "build", "validate", "ingest", "verify", "report", "run"]:
        sp = sub.add_parser(name)
        sp.add_argument("--print-json", action="store_true")

    args = p.parse_args()

    if args.command == "preflight":
        return cmd_not_implemented("preflight")
    if args.command == "build":
        return cmd_not_implemented("build")
    if args.command == "validate":
        return cmd_not_implemented("validate")
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
