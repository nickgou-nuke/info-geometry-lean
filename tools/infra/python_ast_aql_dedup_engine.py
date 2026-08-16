#!/usr/bin/env python3
"""
CLI Runner for ArangoDB AST AQL Deduplication and Equivalence Clustering Engine.
Discovers exact and structural AST equivalence classes via ArangoDB graph queries.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_REPO_ROOT / "src"))
sys.path.insert(0, str(_REPO_ROOT))

from igf.cpg.dedup import ArangoCPGDeduplicator


def main() -> int:
    parser = argparse.ArgumentParser(description="AST AQL Deduplication and Equivalence Clustering Engine")
    parser.add_argument("--out", type=str, default="reports/cpg_dedup_report.json", help="Output JSON report path")
    parser.add_argument("--min-count", type=int, default=2, help="Minimum cluster cardinality")
    parser.add_argument("--limit", type=int, default=100, help="Maximum clusters to report per category")
    args = parser.parse_args()

    print("=== [cpg-dedup] Starting AST AQL Equivalence Discovery in ArangoDB ===")
    dedup = ArangoCPGDeduplicator()
    if not dedup.db:
        print("❌ [cpg-dedup] Failed to connect to ArangoDB.")
        return 1

    manifest = dedup.generate_deduplication_manifest(out_json=Path(args.out))
    print(f"✅ [cpg-dedup] Discovered {manifest['summary']['exact_function_clone_clusters']} exact function clone clusters and {manifest['summary']['structural_function_shape_clusters']} structural shape clusters.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
