#!/usr/bin/env bash
set -euo pipefail

# Stable build wrapper to reduce rebuild contention during active development.
# Usage:
#   scripts/build/stable-canonical.sh
#   scripts/build/stable-canonical.sh InfoGeometry.Canonical.AnalyticalIndex
#   scripts/build/stable-canonical.sh InfoGeometry.Convex.SpinFactorHessian

JOBS="${LAKE_NUM_JOBS:-6}"
export LAKE_NUM_JOBS="$JOBS"

echo "[stable-build] LAKE_NUM_JOBS=$LAKE_NUM_JOBS"

if [ "$#" -eq 0 ]; then
  echo "[stable-build] Building changed Lean owner modules incrementally"
  exec python3 tools/infra/build_changed_lean.py --wait-for-build-lock
fi

echo "[stable-build] Building targets: $* --wfail"
exec python3 tools/run_locked_lake_build.py "$@" --wfail
