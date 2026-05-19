#!/usr/bin/env python3
from __future__ import annotations

"""Thin wrapper around the unified GraphRAG explorer.

This is the user-facing natural-language entrypoint for repository exploration.
It searches Lean declarations, docs, black books, handover material, and
external mirrors, while keeping Lean/kernel proof authority separate.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "tools" / "infra" / "graph_rag_query.py"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", help="Natural-language question or keyword query")
    parser.add_argument("--top-k", type=int, default=8)
    parser.add_argument("--format", choices=["md", "json"], default="md")
    parser.add_argument("--brief", action="store_true", help="Render a compact provenance summary instead of raw explorer output")
    parser.add_argument("--scope", choices=["all", "lean", "docs", "external", "gravity"], default="all")
    parser.add_argument("--no-gravity", action="store_true")
    parser.add_argument("--lean-records", type=Path, default=None)
    parser.add_argument("--external-root", type=Path, default=None)
    parser.add_argument("--black-books-root", type=Path, default=None)
    parser.add_argument("--handover-root", type=Path, default=None)
    return parser.parse_args()


def build_cmd(args: argparse.Namespace) -> list[str]:
    fmt = "json" if args.brief else args.format
    cmd = [
        sys.executable,
        str(SCRIPT),
        args.query,
        "--top-k",
        str(args.top_k),
        "--format",
        fmt,
        "--scope",
        args.scope,
    ]
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
    return cmd


def _count(items: list[dict[str, Any]]) -> int:
    return sum(1 for item in items if isinstance(item, dict))


def render_brief(payload: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Repo provenance summary")
    lines.append("")
    lines.append(f"Query: `{payload.get('query', '')}`")
    lines.append("")

    lean = [item for item in payload.get("lean", []) if isinstance(item, dict)]
    docs = [item for item in payload.get("docs", []) if isinstance(item, dict)]
    external = [item for item in payload.get("external", []) if isinstance(item, dict)]
    gravity = payload.get("gravity")

    lines.append("## Source breakdown")
    lines.append("")
    lines.append(f"- Lean declarations: `{len(lean)}`")
    lines.append(f"- Docs / black books / handover: `{len(docs)}`")
    lines.append(f"- External mirrors: `{len(external)}`")
    lines.append(f"- Gravity context: `{ 'available' if isinstance(gravity, dict) else 'disabled' }`")
    lines.append("")

    def add_top(title: str, items: list[dict[str, Any]]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        if not items:
            lines.append("- no hits")
            lines.append("")
            return
        for idx, item in enumerate(items[:3], start=1):
            name = item.get("title") or item.get("name") or item.get("module") or "item"
            source = item.get("source") or "unknown"
            path = item.get("path") or ""
            score = item.get("score")
            lines.append(f"{idx}. `{name}` [{source}] score={score}")
            if path:
                lines.append(f"   - path: `{path}`")
            snippet = item.get("snippet")
            if isinstance(snippet, str) and snippet:
                lines.append(f"   - excerpt: {snippet[:240]}")
        lines.append("")

    add_top("Lean", lean)
    add_top("Docs / black books / handover", docs)
    add_top("External mirrors", external)

    if isinstance(gravity, dict):
        lines.append("## Gravity context")
        lines.append("")
        if gravity.get("ok"):
            payload_g = gravity.get("payload", {})
            items = payload_g.get("items") or []
            lines.append(f"- graph source: `{payload_g.get('graph_source', 'unknown')}`")
            lines.append(f"- item count: `{len(items)}`")
            for idx, item in enumerate(items[:3], start=1):
                if not isinstance(item, dict):
                    continue
                name = item.get("name") or item.get("decl") or item.get("id") or "item"
                score = item.get("score") or item.get("weight") or item.get("rank") or "?"
                path = item.get("file") or item.get("path") or ""
                lines.append(f"{idx}. `{name}` score={score} path=`{path}`")
        else:
            lines.append(f"- unavailable: {gravity.get('error')}")
        lines.append("")

    lines.append("Authority labels:")
    lines.append("- Lean = proof/navigation authority")
    lines.append("- Docs/black books/handover = retrieval context")
    lines.append("- External mirrors = search-only mirrors")
    lines.append("- Gravity = graph navigation context only")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    cmd = build_cmd(args)
    proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr or proc.stdout)
        return proc.returncode

    if args.brief:
        payload = json.loads(proc.stdout)
        print(render_brief(payload))
        return 0

    sys.stdout.write(proc.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
