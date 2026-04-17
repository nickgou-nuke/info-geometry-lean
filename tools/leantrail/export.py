#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.leantrail.adapters import (
    export_arango_json,
    export_graphml,
    export_neo4j_csv,
    load_snapshot,
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export LeanTrail snapshot to external analyzer formats."
    )
    parser.add_argument(
        "--snapshot",
        default="artifacts/leantrail/graph_snapshot.json",
        help="Input LeanTrail snapshot JSON path.",
    )
    parser.add_argument(
        "--to",
        choices=["graphml", "neo4j-csv", "arango-json", "all"],
        default="all",
        help="Export target format.",
    )
    parser.add_argument(
        "--graphml-out",
        default="artifacts/leantrail/graph_snapshot.graphml",
        help="GraphML output path.",
    )
    parser.add_argument(
        "--neo4j-out-dir",
        default="artifacts/leantrail/neo4j",
        help="Neo4j CSV output directory.",
    )
    parser.add_argument(
        "--arango-out-dir",
        default="artifacts/leantrail/arango",
        help="Arango JSON export directory.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    snapshot_path = Path(args.snapshot).resolve()
    if not snapshot_path.exists():
        raise FileNotFoundError(f"Snapshot not found: {snapshot_path}")
    snapshot = load_snapshot(snapshot_path)

    wrote = 0
    if args.to in {"graphml", "all"}:
        graphml_out = Path(args.graphml_out).resolve()
        export_graphml(snapshot, graphml_out)
        print(f"GraphML export written: {graphml_out}")
        wrote += 1

    if args.to in {"neo4j-csv", "all"}:
        neo4j_out = Path(args.neo4j_out_dir).resolve()
        export_neo4j_csv(snapshot, neo4j_out)
        print(f"Neo4j CSV export written: {neo4j_out}")
        wrote += 1

    if args.to in {"arango-json", "all"}:
        arango_out = Path(args.arango_out_dir).resolve()
        export_arango_json(snapshot, arango_out)
        print(f"Arango JSON export written: {arango_out}")
        wrote += 1

    if wrote == 0:
        print("No outputs requested.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
