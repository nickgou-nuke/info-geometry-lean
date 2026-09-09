#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed or not on PATH; no Lean elaboration executed.' >&2
  exit 127
fi

python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Streaming.TwoBoundaryWeakPristineChain

log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean lean/InfoGeometry/Streaming/TwoBoundaryWeakAudit.lean | tee "$log"

python3 - "$log" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding='utf-8')
audit = Path('lean/InfoGeometry/Streaming/TwoBoundaryWeakAudit.lean').read_text(encoding='utf-8')
expected = audit.count('#print axioms ')
blocks = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
empty = len(re.findall(r'does not depend on any axioms', text))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

for block in blocks:
    bad = {item.strip() for item in block.split(',') if item.strip()} - allowed
    if bad:
        raise SystemExit('Unexpected transitive axioms: ' + repr(sorted(bad)))

if len(blocks) + empty != expected:
    raise SystemExit(
        f'Incomplete axiom report: expected {expected}, '
        f'parsed {len(blocks) + empty}. Inspect Lean output.'
    )

print(f'Inspected {expected} declarations; only allowed logical axioms reported.')
PY
