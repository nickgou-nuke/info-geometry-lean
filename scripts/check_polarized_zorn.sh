#!/usr/bin/env bash
# Execute from the repository root after checkout/application of the extension.
set -euo pipefail
OUT="reports/polarized-zorn-kernel"
mkdir -p "$OUT"
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'NOT KERNEL CHECKED: lake is not installed or not on PATH.' | tee "$OUT/lean-attempt.log"
  exit 127
fi
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.PolarizedZornReconstruction
lake env lean lean/InfoGeometry/Canonical/PolarizedZornReconstructionAudit.lean 2>&1 | tee "$OUT/axioms.log"
python3 - "$OUT/axioms.log" <<'PY'
import re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
audit=Path('lean/InfoGeometry/Canonical/PolarizedZornReconstructionAudit.lean').read_text()
expected=re.findall(r'^#print axioms (\S+)',audit,re.M)
allowed={'propext','Classical.choice','Quot.sound'}
for name in expected:
    m=re.search(r"'?"+re.escape(name)+r"'?\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",text,re.S)
    if not m: raise SystemExit('FAIL: missing axiom report for '+name)
    actual=set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',m.group(1) or ''))
    if not actual<=allowed:
        raise SystemExit('FAIL: unapproved transitive axioms for '+name+': '+str(actual-allowed))
print('PASS:',len(expected),'complete transitive axiom reports; only approved logical axioms.')
PY
