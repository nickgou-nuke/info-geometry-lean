#!/usr/bin/env bash
set -euo pipefail

# Current declaration-DAG baseline.
# This script deliberately avoids the archived docs-map/module_graph lane.
# Steps kept here:
# 1) locked public build
# 2) authoritative declaration-DAG refresh
# 3) rooted causal-order / coverage refresh
# 4) missing-All classification refresh

python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
python3 tools/infra/classify_missing_all.py
