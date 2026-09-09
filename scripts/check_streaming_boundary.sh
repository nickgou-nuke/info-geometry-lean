#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed or not on PATH; no Lean elaboration executed.' >&2
  exit 127
fi
lake build InfoGeometry.Streaming.StreamingBoundaryPristineChain
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean lean/InfoGeometry/Streaming/StreamingBoundaryAudit.lean | tee "$log"
python3 - "$log" <<'PY'
from pathlib import Path
import re,sys
text=Path(sys.argv[1]).read_text()
expected=Path('lean/InfoGeometry/Streaming/StreamingBoundaryAudit.lean').read_text().count('#print axioms ')
blocks=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text,re.S)
empty=len(re.findall(r'does not depend on any axioms',text))
allowed={'propext','Classical.choice','Quot.sound'}
for block in blocks:
    bad={a.strip() for a in block.split(',') if a.strip()}-allowed
    if bad:raise SystemExit('Unexpected transitive axioms: '+repr(sorted(bad)))
if len(blocks)+empty!=expected:
    raise SystemExit(f'Incomplete axiom report: expected {expected}, parsed {len(blocks)+empty}. Inspect Lean output.')
print(f'Inspected {expected} declarations; only allowed logical axioms reported.')
PY

