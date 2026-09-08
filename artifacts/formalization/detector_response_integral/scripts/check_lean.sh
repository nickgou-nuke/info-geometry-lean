#!/usr/bin/env bash
# Compile the candidate overlay into a fresh directory. Never modify the owner
# files, invoke lake clean, or discard existing build products.
set -euo pipefail
bundle=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo=${1:?Usage: check_lean.sh /path/to/info-geometry-lean [--bridge]}
bridge=${2:-}
command -v lake >/dev/null 2>&1 || { echo 'NOT RUN: lake is unavailable.' >&2; exit 127; }
[[ -f "$repo/lean-toolchain" ]] || { echo 'Missing repository lean-toolchain.' >&2; exit 2; }
[[ -z "$bridge" || "$bridge" == --bridge ]] || { echo 'Unknown second argument.' >&2; exit 2; }
cd -- "$repo"
[[ "$(tr -d '\r\n' < lean-toolchain)" == leanprover/lean4:v4.28.1 ]] || {
  echo 'Toolchain differs from inspected v4.28.1; review compatibility first.' >&2; exit 2;
}
python3 - <<'PY'
import json
from pathlib import Path
m = json.loads(Path('lake-manifest.json').read_text())
rev = next(x['rev'] for x in m['packages'] if x['name'] == 'mathlib')
if rev != '8f9d9cff6bd728b17a24e163c9402775d9e6a365':
    raise SystemExit('Mathlib differs from the inspected pin; review compatibility first.')
PY
scratch=$(mktemp -d "${TMPDIR:-/tmp}/detector-response-check.XXXXXXXX")
echo "Build products and logs: $scratch"
lean_prefix=$(lake env lean --print-prefix)
deps=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$scratch${deps:+:$deps}"
lean_bin="$lean_prefix/bin/lean"
modules=(DetectorTransportKernel DetectorVolumeResponse DetectorBeerLambert DetectorDiskIntegral
         DetectorResponseCore DetectorResponseAudit)
if [[ "$bridge" == --bridge ]]; then
  modules+=(DetectorResponseIntegral DetectorResponseBridgeAudit)
fi
for module in "${modules[@]}"; do
  path="InfoGeometry/Nuclear/$module"
  mkdir -p "$scratch/$(dirname -- "$path")"
  "$lean_bin" --root="$bundle/lean" -o "$scratch/$path.olean" "$bundle/lean/$path.lean" 2>&1 | tee "$scratch/$module.log"
done
if grep -E '\bsorryAx\b|\bLean.ofReduceBool\b' "$scratch"/*Audit.log; then
  echo 'Unacceptable proof dependency in transitive axiom report.' >&2
  exit 1
fi
echo 'Selected modules elaborated and kernel-checked. Inspect all emitted axiom reports and warnings.'
