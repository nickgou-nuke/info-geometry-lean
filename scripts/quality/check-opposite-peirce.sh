#!/usr/bin/env bash
set -euo pipefail

# Existing source-closure compiler owns the shared build lock and axiom gate.
# Root dependency pins and sources are never updated by this scoped check.
repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
: "${RUNNER_TEMP:?Set RUNNER_TEMP to a disposable verification directory}"
proof_mathlib="$RUNNER_TEMP/opposite-peirce-proof-mathlib"
python3 - "$proof_mathlib" <<'PY'
import json
from pathlib import Path
import subprocess
import sys
pin = next(p for p in json.loads(Path('lake-manifest.json').read_text())['packages']
           if p['name'] == 'mathlib')
root = Path(sys.argv[1])
if not (root / '.git').is_dir():
    subprocess.run(['git', 'init', str(root)], check=True)
    subprocess.run(['git', '-C', str(root), 'remote', 'add', 'origin', pin['url']], check=True)
    subprocess.run(['git', '-C', str(root), 'fetch', '--depth=1', 'origin', pin['rev']], check=True)
    subprocess.run(['git', '-C', str(root), 'checkout', '--detach', 'FETCH_HEAD'], check=True)
PY
python3 tools/quality/check_opposite_peirce.py \
  --mathlib-root "$proof_mathlib" --output .artifacts/opposite-peirce
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/NCG/OppositePeirceCoupling.lean \
  lean/InfoGeometry/NCG/OppositePeirceTrace.lean \
  lean/InfoGeometry/NCG/OppositePeirceRealMetric.lean \
  lean/InfoGeometry/NCG/OppositePeirceWitness.lean \
  lean/InfoGeometry/NCG/OppositePeirceOrder.lean \
  --fail-on error --json-out .artifacts/opposite-peirce/vacuity.json
