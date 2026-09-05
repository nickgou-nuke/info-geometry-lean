#!/usr/bin/env bash
# Sequential compilation and transitive axiom audit. No dependency updates or cache cleaning.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'UNVERIFIED: lake is unavailable; no Lean check was performed.' >&2
  exit 2
fi
if [[ ! -f lean-toolchain || ! -f lake-manifest.json ]]; then
  printf '%s\n' 'Run this check inside the repository with its existing pinned toolchain and manifest.' >&2
  exit 2
fi
mkdir -p reports
if [[ ! -f tools/infra/run_locked_lake_build.py ]]; then
  printf '%s\n' 'Repository build-lock owner missing; refusing to bypass sequential build coordination.' >&2
  exit 2
fi
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.ZornRindlerReconstruction \
  2>&1 | tee reports/zorn-rindler-build.log
# The build completed before this second, sequential Lean invocation.
lake env lean tests/ZornRindlerAxiomAudit.lean \
  2>&1 | tee reports/zorn-rindler-axioms.log
python3 - <<'PY'
import re
from pathlib import Path
expected = set(re.findall(r'^#print axioms (\S+)',
    Path('tests/ZornRindlerAxiomAudit.lean').read_text(), re.M))
log = Path('reports/zorn-rindler-axioms.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
seen = set()
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S):
    seen.add(name)
    bad = {a.strip() for a in axioms.split(',') if a.strip()} - allowed
    if bad:
        raise SystemExit(f'UNACCEPTED AXIOMS for {name}: {sorted(bad)}')
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
missing = expected - seen
if not expected or missing:
    raise SystemExit(f'INCOMPLETE AXIOM READBACK: {sorted(missing)}')
print(f'Native Lean build and {len(expected)} transitive theorem axiom checks passed.')
PY
