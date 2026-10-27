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
proof_mathlib="$RUNNER_TEMP/rectangular-proof-mathlib"
proof_oleans="$RUNNER_TEMP/rectangular-proof-oleans"
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
  lake exe cache get Mathlib/Tactic.lean Mathlib/LinearAlgebra/Matrix/Rank.lean \
    Mathlib/LinearAlgebra/Projection.lean Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean
)
mathlib_lean_path=$(cd "$proof_mathlib" && lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_oleans:$mathlib_lean_path"
mkdir -p .artifacts/rectangular-peirce
modules=(
  InfoGeometry.Algebra.FiniteSpinAlgebra
  InfoGeometry.Core.PeirceDecomposition
  InfoGeometry.QuantumContext.DrazinSpectralKernel
  InfoGeometry.Algebra.RectangularRetract
  InfoGeometry.QuantumContext.RectangularDrazinLift
  InfoGeometry.QuantumContext.RectangularPeirceDrazin
  InfoGeometry.QuantumContext.RectangularPeirceDrazinAudit
)
for module in "${modules[@]}"; do
  relative_path=${module//./\/}
  mkdir -p "$proof_oleans/$(dirname "$relative_path")"
  echo "CHECK $module"
  lean --root="$repo_root/lean" -o "$proof_oleans/$relative_path.olean" \
    "$repo_root/lean/$relative_path.lean" 2>&1 | tee ".artifacts/rectangular-peirce/$module.log"
done
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/Algebra/RectangularRetract.lean \
  lean/InfoGeometry/QuantumContext/RectangularDrazinLift.lean \
  lean/InfoGeometry/QuantumContext/RectangularPeirceDrazin.lean --fail-on error \
  --json-out .artifacts/rectangular-peirce/vacuity.json
sha256sum lean/InfoGeometry/Algebra/RectangularRetract.lean \
  lean/InfoGeometry/QuantumContext/RectangularDrazinLift.lean \
  lean/InfoGeometry/QuantumContext/RectangularPeirceDrazin.lean \
  lean/InfoGeometry/QuantumContext/RectangularPeirceDrazinAudit.lean
