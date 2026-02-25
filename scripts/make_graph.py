#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any

from tools.pathing import normalize_user_path, default_docs_map_root


def run_export(import_mods: str, out: Path, ns_prefix: str = "InfoGeometry") -> None:
    # invoke the Lean exporter via lake env lean --run
    cmd = [
        "lake",
        "env",
        "lean",
        "--run",
        "scripts/ExportGraph.lean",
        import_mods,
        str(out),
        ns_prefix,
    ]
    subprocess.run(cmd, check=True)


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--modules", default="InfoGeometry.Library,InfoGeometry.Research.All", help="Comma-separated modules to load")
    ap.add_argument("--ns", default="InfoGeometry", help="Namespace prefix to filter by")
    ap.add_argument("--out", default=None, help="Output JSON path")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    out_path = normalize_user_path(args.out, docs_root / "graph.json")

    run_export(args.modules, out_path, args.ns)

    # Report a quick summary of node/edge counts; attempt to parse the JSON
    try:
        data = load_json(out_path)
        nodes = data.get("nodes", [])
        edges = data.get("edges", [])
        edge_count = len(edges)
        # edges may be triples (from,to,kind) or pairs
        if edge_count > 0 and isinstance(edges[0], list) and len(edges[0]) == 3:
            kinds = {e[2] for e in edges}
            print(f"[make_graph] exported graph with {len(nodes)} nodes, {edge_count} edges (kinds={kinds})")
        else:
            print(f"[make_graph] exported graph with {len(nodes)} nodes, {edge_count} edges")
    except Exception:
        print(f"[make_graph] exported graph to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
