#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed or not on PATH; no Lean elaboration executed.' >&2
  exit 127
fi

lake build InfoGeometry.Orthogonal.O55ContactFullFormalism

log=$(mktemp)
trap 'rm -f "$log"' EXIT

lake env lean lean/InfoGeometry/Orthogonal/O55ContactAudit.lean | tee "$log"

python3 - "$log" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
audit = Path('lean/InfoGeometry/Orthogonal/O55ContactAudit.lean').read_text()
expected = audit.count('#print axioms ')

blocks = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
empty = len(re.findall(r'does not depend on any axioms', text))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

for block in blocks:
    found = {item.strip() for item in block.split(',') if item.strip()}
    bad = found - allowed
    if bad:
        raise SystemExit('Unexpected transitive axioms: ' + repr(sorted(bad)))

reported = len(blocks) + empty
if reported != expected:
    raise SystemExit(
        f'Incomplete axiom report: expected {expected}, parsed {reported}. '
        'Inspect Lean output.'
    )

if 'declaration uses \'sorry\'' in text.lower() or 'sorryAx' in text:
    raise SystemExit('Lean reported a sorry dependency.')

print(f'Inspected {expected} declarations; only allowed logical axioms reported.')
PY
