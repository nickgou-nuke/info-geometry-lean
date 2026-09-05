#!/usr/bin/env bash
# Run in an idle checkout with the repository's pinned dependencies installed.
# Sequential narrow build followed by a fresh transitive axiom readout.
set -euo pipefail
cd "$(dirname "$0")/../.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake is unavailable; no Lean check was performed.' >&2
  exit 2
fi
if [[ ! -f tools/infra/run_locked_lake_build.py ]]; then
  echo 'Run this script from the complete repository checkout.' >&2
  exit 2
fi
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.OperatorZornGaugeCovariance
log="$(mktemp)"
trap 'rm -f "$log"' EXIT
lake env lean tests/OperatorZornGaugeAxiomAudit.lean >"$log" 2>&1
cat "$log"
python3 - "$log" <<'PY'
import pathlib,re,sys
text=pathlib.Path(sys.argv[1]).read_text()
audit=pathlib.Path('tests/OperatorZornGaugeAxiomAudit.lean').read_text()
expected=set(re.findall(r'^#print axioms (\S+)',audit,re.M))
allowed={'propext','Classical.choice','Quot.sound'}
found={}
for m in re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.S):
    found[m.group(1)]={x.strip() for x in (m.group(2) or '').split(',') if x.strip()}
missing=expected-set(found)
bad={n:sorted(found[n]-allowed) for n in expected & set(found) if found[n]-allowed}
if missing or bad or re.search(r'\b(?:error|warning):',text):
    raise SystemExit(f'FAIL: missing={sorted(missing)}; unexpected_axioms={bad}; inspect diagnostics above')
print(f'PASS: all {len(expected)} theorem readouts present; only the allowed foundational axioms.')
PY
