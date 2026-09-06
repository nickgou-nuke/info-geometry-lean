#!/usr/bin/env bash
# Run in an idle complete checkout with its pinned dependencies.
# This command performs no dependency update or cache deletion.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 tools/quality/audit_zorn_twin_sources.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake is unavailable; no Lean elaboration or kernel audit ran.' >&2
  exit 2
fi
if [[ ! -f tools/infra/run_locked_lake_build.py ]]; then
  echo 'UNVERIFIED: a complete repository checkout is required.' >&2
  exit 2
fi
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.OperatorZornTwinCyclotomic
log="$(mktemp)"
trap 'rm -f "$log"' EXIT
if ! lake env lean tests/OperatorZornTwinCyclotomicAxiomAudit.lean >"$log" 2>&1; then
  cat "$log" >&2
  exit 1
fi
cat "$log"
python3 - "$log" <<'PY'
import pathlib,re,sys
text=pathlib.Path(sys.argv[1]).read_text()
audit=pathlib.Path('tests/OperatorZornTwinCyclotomicAxiomAudit.lean').read_text()
expected=set(re.findall(r'^#print axioms (\S+)',audit,re.M))
allowed={'propext','Classical.choice','Quot.sound'}
found={}
for m in re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.S):
    found[m.group(1)]={x.strip() for x in (m.group(2) or '').split(',') if x.strip()}
missing=expected-set(found)
bad={n:sorted(found[n]-allowed) for n in expected & set(found) if found[n]-allowed}
if not expected or missing or bad or re.search(r'\b(?:error|warning):',text):
    raise SystemExit(f'FAIL: missing={sorted(missing)}; unexpected_axioms={bad}; inspect diagnostics above')
print(f'PASS: all {len(expected)} declaration readouts contain only the permitted foundational axioms')
PY
