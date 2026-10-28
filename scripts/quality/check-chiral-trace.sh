#!/usr/bin/env bash
set -euo pipefail

# Isolated pinned-mathlib check. Does not replace or update the root Lake manifest.
repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
exec 9>/tmp/info-geometry-build.lock
flock 9
if pgrep -x 'lean|lake|leanc' >/dev/null; then
  echo 'Another compiler is active; refusing concurrent verification.' >&2
  exit 2
fi
proof_mathlib="$RUNNER_TEMP/chiral-proof-mathlib"
proof_oleans="$RUNNER_TEMP/chiral-proof-oleans"
mathlib_rev=$(python3 - <<'PY'
import json
with open('lake-manifest.json') as f:
    print(next(p['rev'] for p in json.load(f)['packages'] if p['name'] == 'mathlib'))
PY
)
lean --version
lake --version
git rev-parse HEAD
if [ ! -d "$proof_mathlib/.git" ]; then
  git init "$proof_mathlib"
  git -C "$proof_mathlib" remote add origin https://github.com/leanprover-community/mathlib4.git
  git -C "$proof_mathlib" fetch --depth 1 origin "$mathlib_rev"
  git -C "$proof_mathlib" checkout --detach FETCH_HEAD
fi
test "$(git -C "$proof_mathlib" rev-parse HEAD)" = "$mathlib_rev"
test "$(cat lean-toolchain)" = "$(cat "$proof_mathlib/lean-toolchain")"
(
  cd "$proof_mathlib"
  lake exe cache get Mathlib/Tactic.lean Mathlib/LinearAlgebra/Matrix/Trace.lean \
    Mathlib/LinearAlgebra/Projection.lean Mathlib/LinearAlgebra/Matrix/ToLin.lean \
    Mathlib/LinearAlgebra/Eigenspace/Basic.lean Mathlib/Algebra/Star/StarProjection.lean \
    Mathlib/Algebra/Lie/OfAssociative.lean
)
mathlib_lean_path=$(cd "$proof_mathlib" && lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_oleans:$mathlib_lean_path"
mkdir -p .artifacts/chiral-trace
modules=(
  InfoGeometry.Algebra.FiniteSpinAlgebra
  InfoGeometry.Core.PeirceDecomposition
  InfoGeometry.Core.PeirceGrading
  InfoGeometry.NCG.NonCommutativeFredholmIndex
  InfoGeometry.QuantumContext.DrazinSpectralKernel
  InfoGeometry.NCG.ChiralMatrixTrace
  InfoGeometry.NCG.PartialPhaseLocalization
  InfoGeometry.NCG.ChiralTraceAudit
)
for module in "${modules[@]}"; do
  relative_path=${module//./\/}
  mkdir -p "$proof_oleans/$(dirname "$relative_path")"
  echo "CHECK $module"
  lean --root="$repo_root/lean" -o "$proof_oleans/$relative_path.olean" \
    "$repo_root/lean/$relative_path.lean" 2>&1 | tee ".artifacts/chiral-trace/$module.log"
done
python3 - <<'AXIOM_AUDIT'
import re
from pathlib import Path
sources = [
    Path('lean/InfoGeometry/NCG/ChiralMatrixTrace.lean'),
    Path('lean/InfoGeometry/NCG/PartialPhaseLocalization.lean'),
]
expected = set()
for source in sources:
    text = source.read_text()
    namespace = re.search(r'^namespace (\S+)', text, re.M).group(1)
    expected.update(namespace + '.' + name for name in
                    re.findall(r'^(?:@\[simp\] )?theorem (\w+)', text, re.M))
log = Path('.artifacts/chiral-trace/InfoGeometry.NCG.ChiralTraceAudit.log').read_text()
reports = {}
for name, dependencies in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
    reports[name] = {x.strip() for x in dependencies.split(',') if x.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    reports[name] = set()
assert set(reports) == expected, (expected - set(reports), set(reports) - expected)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, dependencies in reports.items():
    assert dependencies <= allowed, (name, dependencies - allowed)
print(f'AXIOM_AUDIT_PASS: {len(reports)} declarations; only standard Lean foundations')
AXIOM_AUDIT
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/NCG/ChiralMatrixTrace.lean \
  lean/InfoGeometry/NCG/PartialPhaseLocalization.lean \
  --fail-on error \
  --json-out .artifacts/chiral-trace/vacuity.json
sha256sum lean/InfoGeometry/NCG/ChiralMatrixTrace.lean \
  lean/InfoGeometry/NCG/PartialPhaseLocalization.lean \
  lean/InfoGeometry/NCG/ChiralTraceAudit.lean
