#!/usr/bin/env python3
from __future__ import annotations

"""Thin wrapper around the unified GraphRAG explorer.

This is the user-facing natural-language entrypoint for repository exploration.
It searches Lean declarations, docs, black books, handover material, and
external mirrors, while keeping Lean/kernel proof authority separate.
"""

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "tools" / "infra" / "graph_rag_query.py"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", help="Natural-language question or keyword query")
    parser.add_argument("--top-k", type=int, default=8)
    parser.add_argument("--format", choices=["md", "json"], default="md")
    parser.add_argument("--no-gravity", action="store_true")
    parser.add_argument("--lean-records", type=Path, default=None)
    parser.add_argument("--external-root", type=Path, default=None)
    parser.add_argument("--black-books-root", type=Path, default=None)
    parser.add_argument("--handover-root", type=Path, default=None)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    cmd = [sys.executable, str(SCRIPT), args.query, "--top-k", str(args.top_k), "--format", args.format]
    if args.no_gravity:
        cmd.append("--no-gravity")
    if args.lean_records is not None:
        cmd.extend(["--lean-records", str(args.lean_records)])
    if args.external_root is not None:
        cmd.extend(["--external-root", str(args.external_root)])
    if args.black_books_root is not None:
        cmd.extend(["--black-books-root", str(args.black_books_root)])
    if args.handover_root is not None:
        cmd.extend(["--handover-root", str(args.handover_root)])

    proc = subprocess.run(cmd, cwd=ROOT)
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
