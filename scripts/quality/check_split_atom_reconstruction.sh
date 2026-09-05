#!/usr/bin/env bash
# Sequential, non-destructive verification with the repository's pinned toolchain.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null || { echo 'Lake is unavailable; no kernel check was performed.' >&2; exit 2; }
if pgrep -x lean >/dev/null || pgrep -x lake >/dev/null; then
  echo 'Another Lean/Lake process is active; run this check on an idle worktree.' >&2
  exit 3
fi
lake build InfoGeometry.Canonical.SplitAtomReconstruction
log="$(mktemp "${TMPDIR:-/tmp}/split-atom-axioms.XXXXXX.log")"
lake env lean tests/SplitAtomAxiomAudit.lean 2>&1 | tee "$log"
python3 - "$log" <<'PY'
from pathlib import Path
import re
import sys
text = Path(sys.argv[1]).read_text()
expected = Path('tests/SplitAtomAxiomAudit.lean').read_text().count('#print axioms ')
sets = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
empty = text.count('does not depend on any axioms')
if len(sets) + empty != expected:
    raise SystemExit(f'Incomplete axiom output: expected {expected}, found {len(sets)+empty}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
used = {a.strip() for group in sets for a in group.split(',') if a.strip()}
if used - allowed:
    raise SystemExit(f'Unapproved transitive axioms: {sorted(used-allowed)}')
print(f'Kernel build and transitive axiom checks passed for {expected} new theorems.')
PY
printf 'Axiom log: %s\n' "$log"
