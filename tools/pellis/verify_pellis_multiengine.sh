#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 tools/sympy/pellis_golden_alpha_sympy.py
sage tools/sage/pellis_golden_alpha.sage
gap -b tools/infra/pellis_golden_alpha_gap.g
M2 -q -e 'input "tools/infra/pellis_golden_alpha_macaulay2.m2"'
~/.elan/bin/lake env lean /home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/PellisGoldenAlpha.lean
/home/goutev/.opam/coq-switch/bin/coqc tools/infra/bridge_data/PellisGoldenAlpha.v
cd isabelle && /usr/local/bin/isabelle build -D . -b InfoGeometry
