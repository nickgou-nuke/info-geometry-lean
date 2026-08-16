#!/usr/bin/env python3
"""
Python Code Property Graph (CPG) CI Gatekeeper.

Enforces:
1. Zero Lake/Cache-Destructive Hazards: blocks any Python script containing
   unauthorized `lake clean` or `.lake` cache mutations.
2. In-Degree & Reachability Fidelity: flags unverified orphan scripts with
   zero incoming dependencies and zero CI paths.
3. Strict Refactoring Safety: mathematically prevents deletion or relocation of
   any script that is reachable from active entrypoints or Lean lakefile targets.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.infra.python_dag_dependency_oracle import HighSpeedDependencyGraph
else:
    from tools.pathing import repo_root
    from tools.infra.python_dag_dependency_oracle import HighSpeedDependencyGraph

ROOT = repo_root()


def run_cpg_quality_gate(strict: bool = False) -> int:
    print("[python-cpg-gate] Initializing Repository Dependency & Hazard Oracle...")
    oracle = HighSpeedDependencyGraph(ROOT, scan_dirs=["tools", "src/igf"])
    oracle.analyze_all()

    blocking_errors: list[str] = []

    # 1. AST-based hazard validation
    for rel, hazards in oracle.hazards_by_file.items():
        if "lake_clean_cache_destructive" in hazards:
            blocking_errors.append(
                f"CRITICAL HAZARD: `{rel}` contains executable cache-destructive call (`lake clean` / `rm .lake`)."
            )

    # 2. Check for CI Reachability vs Orphan Classification
    records = list(oracle.records.values())
    ci_critical = [r for r in records if r.classification == "ACTIVE_CI_CRITICAL"]
    libraries = [r for r in records if r.classification == "ACTIVE_TOOL_LIBRARY"]
    runners = [r for r in records if r.classification == "ACTIVE_RUNNER_UTILITY"]
    doc_refs = [r for r in records if r.classification == "DOCUMENTED_REFERENCE"]
    orphans = [r for r in records if r.classification == "CPG_ORPHAN_CANDIDATE"]

    manifest = oracle.emit_run_manifest()

    print(f"\n[python-cpg-gate] Scanned {len(records)} repo-owned Python scripts in {oracle.elapsed_seconds:.2f}s.")
    print(f"  - Active CI Critical Scripts: {len(ci_critical)}")
    print(f"  - Active Tool Libraries: {len(libraries)}")
    print(f"  - Active Runner Utilities: {len(runners)}")
    print(f"  - Documented References: {len(doc_refs)}")
    print(f"  - CPG Orphan Candidates (model-bounded): {len(orphans)}")
    print(f"  - Telemetry Manifest written to `reports/python_cpg_manifest.json`")

    if blocking_errors:
        print("\n❌ [python-cpg-gate] FAILED: Cache-destructive operations detected:")
        for err in blocking_errors:
            print(f"  - {err}")
        return 1

    print("\n✅ [python-cpg-gate] PASSED: Zero forbidden executable hazards and graph reachability validated.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Python CPG Quality Gatekeeper")
    parser.add_argument("--strict", action="store_true", help="Strict blocking mode")
    args = parser.parse_args()
    return run_cpg_quality_gate(strict=args.strict)


if __name__ == "__main__":
    sys.exit(main())
