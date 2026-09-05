#!/usr/bin/env bash
# Use an idle complete checkout; no dependency update or cache cleaning.
set -euo pipefail
cd "$(dirname "$0")/../.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake is unavailable; no Lean check was performed.' >&2
  exit 2
fi
if [[ ! -f tools/infra/run_locked_lake_build.py ]]; then
  echo 'UNVERIFIED: the complete repository checkout is required.' >&2
  exit 2
fi
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.ProjectiveZornAttention
log="$(mktemp)"
trap 'rm -f "$log"' EXIT
if ! lake env lean tests/ProjectiveZornAttentionAxiomAudit.lean >"$log" 2>&1; then
  cat "$log" >&2
  exit 1
fi
cat "$log"
python3 - "$log" <<'PY'
import pathlib,re,sys
text=pathlib.Path(sys.argv[1]).read_text()
audit=pathlib.Path('tests/ProjectiveZornAttentionAxiomAudit.lean').read_text()
expected=set(re.findall(r'^#print axioms (\S+)',audit,re.M))
allowed={'propext','Classical.choice','Quot.sound'}
found={}
for m in re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.S):
    found[m.group(1)]={x.strip() for x in (m.group(2) or '').split(',') if x.strip()}
missing=expected-set(found)
bad={n:sorted(found[n]-allowed) for n in expected & set(found) if found[n]-allowed}
if not expected or missing or bad or re.search(r'\b(?:error|warning):',text):
    raise SystemExit(f'FAIL: missing={sorted(missing)}; unexpected_axioms={bad}; inspect diagnostics')
print(f'PASS: {len(expected)} complete declaration readouts with only allowed foundational axioms')
PY
