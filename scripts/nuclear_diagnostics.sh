#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

DIAG="lean/InfoGeometry/Physics/NuclearDiagnostics.lean"
PROFILE="scripts/perf/profile_commands.sh"

FILES=(
  "lean/InfoGeometry/Physics/NuclearCartanProjectorParityBridge.lean"
  "lean/InfoGeometry/Physics/NuclearFiniteCARCartanSolovievBridge.lean"
  "lean/InfoGeometry/Physics/NuclearParityGradedHamiltonian.lean"
  "lean/InfoGeometry/Physics/NuclearSolovievParitySymmetry.lean"
  "lean/InfoGeometry/Physics/NuclearWignerDensityProjectorBridge.lean"
  "lean/InfoGeometry/Physics/NuclearSpectroscopyZ2GradingBridge.lean"
)

echo "[nuclear] Lean toolchain"
lean --version || true
lake --version || true

echo
echo "[nuclear] focused elaboration + #print axioms + vacuity lint"
lake env lean -DmaxHeartbeats=200000 "$DIAG"

echo
echo "[nuclear] source-level sorry/admit scan"
if grep -nE '\b(sorry|admit)\b' "${FILES[@]}"; then
  echo "error: sorry/admit found in nuclear diagnostic surface"
  exit 1
else
  echo "[nuclear] no sorry/admit tokens found in selected production files"
fi

echo
echo "[nuclear] profiler summaries"
for file in "${FILES[@]}"; do
  echo
  echo "===== $file ====="
  bash "$PROFILE" "$file" 12
done

echo
echo "[nuclear] diagnostics completed"
