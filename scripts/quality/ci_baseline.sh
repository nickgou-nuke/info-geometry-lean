#!/usr/bin/env bash
set -euo pipefail

# Current declaration-DAG baseline.
# This script deliberately avoids the archived docs-map/module_graph lane.
# Steps kept here:
# 1) locked public build
# 2) coordinated syntax + declaration/type refresh for Mathlib + InfoGeometry
# 3) rooted causal-order / coverage refresh
# 4) missing-All classification refresh

python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
bash scripts/refresh_mathlib_infogeometry_graphs.sh
python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
python3 tools/infra/classify_missing_all.py
