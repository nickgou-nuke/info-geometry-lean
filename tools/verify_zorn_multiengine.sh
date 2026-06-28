#!/usr/bin/env bash
set -u

ROOT="/home/goutev/repos/info-geometry-lean"
cd "$ROOT"

status=0

run() {
  local name="$1"
  shift
  echo "============================================================"
  echo "[$name]"
  echo "CMD: $*"
  if "$@"; then
    echo "STATUS: PASS"
  else
    local ec=$?
    echo "STATUS: FAIL (exit $ec)"
    status=1
  fi
  echo
}

note() {
  echo "============================================================"
  echo "[$1]"
  echo "$2"
  echo
}

run "lean-zorn-g2trifactor-su3" \
  ~/.elan/bin/lake env lean lean/InfoGeometry/Algebra/Zorn/G2TrifactorSU3.lean

run "lean-discrete-color-bridge" \
  ~/.elan/bin/lake env lean lean/InfoGeometry/Algebra/Zorn/DiscreteColorBridge.lean

run "sympy-split-octonion-multiplication" \
  python3 tools/sympy/split_octonion_multiplication.py

run "sympy-split-octonion-symplectic-foundation" \
  python3 tools/sympy/split_octonion_symplectic_foundation.py

run "sympy-zorn-mersenne-aql-bridge" \
  python3 tools/sympy/zorn_mersenne_aql_bridge.py

run "sympy-g2-2-automorphism-theorem" \
  python3 tools/sympy/g2_2_automorphism_theorem.py

run "python-clifford-smoke" \
  python3 tools/python/clifford_package_braiding_smoke.py

run "sage-zorn-complex-bridge" \
  /home/goutev/miniforge3/envs/sage/bin/sage tools/sage/zorn_complex_bridge.sage

run "gap-g2-su3-stabilizer-qualitative" \
  /home/goutev/miniforge3/envs/sage/bin/gap -b tools/gap/g2_su3_stabilizer.g

run "macaulay2-tripotent-dmodule" \
  M2 -q -e 'input "tools/macaulay2/tripotent_dmodule.m2"'

run "isabelle-infogeometry-session" \
  /home/goutev/Isabelle2025-2/bin/isabelle build -D isabelle

if command -v coqc >/dev/null 2>&1; then
  run "coq-complex-structure-bridge" \
    coqc tools/coq/ComplexStructureBridge.v
else
  note "coq-complex-structure-bridge" "SKIP: coqc not installed on PATH; existing compiled artifacts under tools/coq/*.vo are not reverified in this run."
fi

note "scope-boundary" "This script mixes theorem-safe finite packets (Lean/SymPy exact bridges, finite G2(2) order ledger, AQL artifact generation) with weaker qualitative surfaces (notably tools/gap/g2_su3_stabilizer.g and parts of the Sage narrative script). Treat PASS as execution success, not automatic elevation to full SU(3) or real G2 classification."

exit "$status"
