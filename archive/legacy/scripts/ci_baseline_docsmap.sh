#!/usr/bin/env bash
set -euo pipefail

# LEGACY docs-map baseline.
# This script still exercises the older module-graph lane for compatibility.
# The authoritative declaration DAG refresh path is `python3 tools/infra/refresh_decl_graph.py`.
#
# Steps kept here:
# 1) full build
# 2) graph extraction with per-module probe
# 3) deterministic refactor plan

python3 tools/infra/run_locked_lake_build.py
python3 archive/legacy/scripts/make_graph.py --probe-unresolved --out docs-map/graph.json
python3 archive/legacy/scripts/refactor_plan.py \
  --module-graph docs-map/module_graph.json \
  --errors .artifacts/nonbuildable_errors.json \
  --out docs-map/refactor_plan.md

python3 - <<'PY'
import json
from pathlib import Path

data = json.loads(Path("docs-map/module_graph.json").read_text(encoding="utf-8"))
non_buildable = data.get("non_buildable_modules", [])
offenders = [m for m in non_buildable if not m.startswith("InfoGeometry.Archive.Drafts.")]

if offenders:
    print("[ci_baseline] non-archive non-buildable modules detected:")
    for m in offenders:
        print(f"  - {m}")
    raise SystemExit(1)

print(f"[ci_baseline] OK: {len(non_buildable)} non-buildable modules, all in Archive/Drafts.")
PY
