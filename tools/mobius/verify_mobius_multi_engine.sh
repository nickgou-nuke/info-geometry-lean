#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

run() {
  echo "==> $*"
  "$@"
  echo
}

for cls in hyperbolic parabolic elliptic loxodromic; do
  run python3 tools/mobius/mobius_sympy.py "$cls"
done
for cls in hyperbolic parabolic elliptic loxodromic; do
  run /home/goutev/miniforge3/envs/sage/bin/python3 tools/sage/mobius_sage.py "$cls"
done
for cls in hyperbolic parabolic elliptic loxodromic; do
  run /home/goutev/miniforge3/envs/sage/bin/gap -q -c "PacketName:=\"$cls\";; Read(\"tools/mobius/mobius_gap.g\");"
done
if command -v M2 >/dev/null 2>&1; then
  echo "==> M2 detected but skipped: current CLI enters interactive startup in this environment"
  echo
else
  echo "==> Macaulay2 not available on PATH; skipped"
  echo
fi
run python3 tools/mobius/mobius_clifford.py
run python3 tools/mobius/mobius_galgebra.py
if command -v coqc >/dev/null 2>&1; then
  run coqc tools/coq/MobiusDual2x2.v
else
  echo "==> coqc not available on PATH; skipped"
  echo
fi
run ~/.elan/bin/lake env lean lean/InfoGeometry/Geometry/MobiusDual2x2.lean
if command -v isabelle >/dev/null 2>&1; then
  run isabelle build -D tools/isabelle/mobius
else
  echo "==> isabelle not available on PATH; skipped"
  echo
fi

echo "MOBIUS_MULTI_ENGINE_OK"
