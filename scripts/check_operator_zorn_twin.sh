#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT

if ! python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
    InfoGeometry.OperatorAlgebra.OperatorZornTwinAudit >"$LOG" 2>&1; then
  cat "$LOG" >&2
  exit 1
fi
cat "$LOG"

python3 - "$LOG" <<'PY'
from pathlib import Path
import re
import sys

log = Path(sys.argv[1]).read_text(encoding="utf-8")
audit = Path("lean/InfoGeometry/OperatorAlgebra/OperatorZornTwinAudit.lean").read_text(
    encoding="utf-8"
)
expected = len(re.findall(r"^\s*#print axioms\s+", audit, re.MULTILINE))
blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log, re.S)
empty = len(re.findall(r"does not depend on any axioms", log))
allowed = {"propext", "Classical.choice", "Quot.sound"}

for block in blocks:
    unexpected = {axiom.strip() for axiom in block.split(",") if axiom.strip()} - allowed
    if unexpected:
        raise SystemExit("Unexpected transitive axioms: " + repr(sorted(unexpected)))

reported = len(blocks) + empty
if reported != expected:
    raise SystemExit(
        f"Incomplete axiom report: expected {expected}, parsed {reported}. Inspect Lean output."
    )

print(f"Inspected {expected} declarations; only allowed logical axioms reported.")
PY
