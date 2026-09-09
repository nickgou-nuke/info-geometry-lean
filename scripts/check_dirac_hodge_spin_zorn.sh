#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is not installed or not on PATH; no Lean elaboration executed.' >&2
  exit 127
fi

targets=(
  lean/InfoGeometry/OperatorAlgebra/FaithfulOperatorZornEnvelope.lean
  lean/InfoGeometry/OperatorAlgebra/FiniteTwoTermDiracHodgeZorn.lean
  lean/InfoGeometry/OperatorAlgebra/RealWeylAdjointSpinRepresentation.lean
  lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornGradeIntertwiner.lean
  lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornRestrictedGradeMaps.lean
  lean/InfoGeometry/OperatorAlgebra/Cl55FreudenthalZornLieRepresentation.lean
  lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornIntertwinerClosure.lean
  lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAll.lean
)

for target in "${targets[@]}"; do
  lake env lean "$target"
done

log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean \
  lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAudit.lean | tee "$log"

python3 - "$log" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
audit = Path(
    'lean/InfoGeometry/OperatorAlgebra/DiracHodgeSpinZornAudit.lean'
).read_text()
expected = audit.count('#print axioms ')
blocks = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
empty = len(re.findall(r'does not depend on any axioms', text))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

for block in blocks:
    bad = {a.strip() for a in block.split(',') if a.strip()} - allowed
    if bad:
        raise SystemExit('Unexpected transitive axioms: ' + repr(sorted(bad)))

if len(blocks) + empty != expected:
    raise SystemExit(
        f'Incomplete axiom report: expected {expected}, '
        f'parsed {len(blocks) + empty}. Inspect Lean output.'
    )

print(f'Inspected {expected} declarations; only allowed logical axioms reported.')
PY
