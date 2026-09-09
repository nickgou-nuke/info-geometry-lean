#!/usr/bin/env bash
# Verify the native owners through the repository's shared build lock.
set -euo pipefail
repo=${1:?Usage: check_lean.sh /path/to/info-geometry-lean [--bridge]}
bridge=${2:-}
[[ -z "$bridge" || "$bridge" == --bridge ]] || { echo 'Unknown second argument.' >&2; exit 2; }
cd -- "$repo"
modules=(InfoGeometry.Nuclear.DetectorResponseAudit)
if [[ "$bridge" == --bridge ]]; then
  modules+=(InfoGeometry.Nuclear.DetectorResponseBridgeAudit InfoGeometry.Nuclear.All)
fi
log=$(mktemp "${TMPDIR:-/tmp}/detector-response-build.XXXXXXXX.log")
echo "Build log: $log"
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock "${modules[@]}" 2>&1 | tee "$log"
if grep -E '\bsorryAx\b|\bLean.ofReduceBool\b' "$log"; then
  echo 'Unacceptable proof dependency in build output.' >&2
  exit 1
fi
echo 'Native owner targets checked. Inspect axiom reports and warnings; this is not a master build.'
