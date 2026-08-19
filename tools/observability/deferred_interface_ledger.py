#!/usr/bin/env python3
"""Report deferred-interface declarations and nearby owner/bridge surfaces."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent / "graph_overlay_toolchain" / "graph_overlay" / "scripts"
sys.path.insert(0, str(ROOT))

from lean_graph_overlay import build_graph, decl_nodes, filter_graph_by_prefix  # noqa: E402


def file_role_counts(decls: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = defaultdict(lambda: {"owner": 0, "bridge": 0, "deferred_interface": 0})
    for decl in decls:
        bucket = counts[decl["file"]]
        bucket["owner"] += int(bool(decl.get("is_owner")))
        bucket["bridge"] += int(bool(decl.get("is_bridge")))
        bucket["deferred_interface"] += int(bool(decl.get("is_deferred_interface")))
    return counts


def classify_deferred_interface(decl: dict[str, Any], counts: dict[str, dict[str, int]]) -> str:
    roles = counts[decl["file"]]
    return "ownerless_deferred_interface" if roles["owner"] == 0 and roles["bridge"] == 0 else "bridge_backed_deferred_interface"


def deferred_interface_rows(graph: dict[str, Any]) -> list[dict[str, Any]]:
    decls = decl_nodes(graph)
    counts = file_role_counts(decls)
    rows: list[dict[str, Any]] = []
    for decl in decls:
        if not decl.get("is_deferred_interface"):
            continue
        row = dict(decl)
        roles = counts[decl["file"]]
        row["file_owner_count"] = roles["owner"]
        row["file_bridge_count"] = roles["bridge"]
        row["file_deferred_interface_count"] = roles["deferred_interface"]
        row["status"] = classify_deferred_interface(decl, counts)
        rows.append(row)
    return sorted(rows, key=lambda row: (row["status"], row["file"], row["start_line"], row["fqname"]))


def ranked_ownerless_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    result = [row for row in rows if row["status"] == "ownerless_deferred_interface"]
    result.sort(key=lambda row: (-len(row.get("direct_dependencies") or []), row["fqname"]))
    return result


def write_json(graph: dict[str, Any], rows: list[dict[str, Any]], out: Path) -> None:
    out.write_text(json.dumps({
        "root": graph["root"],
        "stats": graph["stats"],
        "deferred_interface_count": len(rows),
        "deferred_interfaces": rows,
        "ownerless_ranked": ranked_ownerless_rows(rows),
    }, ensure_ascii=False, indent=2), encoding="utf-8")


def write_markdown(graph: dict[str, Any], rows: list[dict[str, Any]], out: Path) -> None:
    lines = ["# Deferred Interface Ledger", "", f"Root: `{graph['root']}", "", "## Summary", "",
             f"- deferred interfaces: **{len(rows)}**",
             f"- ownerless deferred interfaces: **{sum(row['status'] == 'ownerless_deferred_interface' for row in rows)}**", ""]
    lines += ["## Declarations", "", "| declaration | file | status |", "| --- | --- | --- |"]
    lines += [f"| `{row['fqname']}` | `{row['file']}` | `{row['status']}` |" for row in rows]
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", default=Path("lean/InfoGeometry"), type=Path)
    parser.add_argument("--out-dir", default=Path("reports/deferred_interface_ledger"), type=Path)
    parser.add_argument("--filter-prefix", default="")
    parser.add_argument("--wl-rounds", type=int, default=4)
    args = parser.parse_args(argv)
    graph = build_graph(args.root.resolve(), wl_rounds=args.wl_rounds)
    if args.filter_prefix:
        graph = filter_graph_by_prefix(graph, args.filter_prefix)
    rows = deferred_interface_rows(graph)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    write_json(graph, rows, args.out_dir / "deferred_interface_ledger.json")
    write_markdown(graph, rows, args.out_dir / "deferred_interface_ledger.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
