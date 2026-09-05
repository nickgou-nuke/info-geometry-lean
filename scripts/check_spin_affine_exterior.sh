#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed or not on PATH; no Lean elaboration executed.' >&2
  exit 127
fi
lake build InfoGeometry.Canonical.SpinAffineExteriorPristineChain
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean lean/InfoGeometry/Canonical/SpinAffineExteriorAudit.lean | tee "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
expected=Path('lean/InfoGeometry/Canonical/SpinAffineExteriorAudit.lean').read_text().count('#print axioms ')
blocks=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text,re.S)
empty=len(re.findall(r'does not depend on any axioms',text))
allowed={'propext','Classical.choice','Quot.sound'}
for block in blocks:
    unexpected={a.strip() for a in block.split(',') if a.strip()}-allowed
    if unexpected:
        raise SystemExit('Unexpected transitive axioms: '+repr(sorted(unexpected)))
if len(blocks)+empty != expected:
    raise SystemExit(f'Incomplete axiom report: expected {expected}, parsed {len(blocks)+empty}')
print(f'All {expected} public declarations reported only allowed logical axioms.')
PY
