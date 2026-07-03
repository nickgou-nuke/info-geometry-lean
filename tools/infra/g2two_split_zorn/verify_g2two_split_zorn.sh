#!/usr/bin/env bash
set -euo pipefail
~/.elan/bin/lake build InfoGeometry.Algebra.Zorn.G2TwoSplitZorn
~/.elan/bin/lake build InfoGeometry.Algebra.Zorn.RealSplitOctonionG2Classification
~/.elan/bin/lake env lean lean/InfoGeometry/Algebra/All.lean
~/.elan/bin/lake env lean lean/InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean
~/.elan/bin/lake env lean lean/InfoGeometry/OperatorAlgebra/SplitOctonionG2TypeGenerators.lean
~/.elan/bin/lake env lean lean/InfoGeometry/Algebra/Zorn/SplitOctonionG2ClassificationCertificate.lean
python3 tools/sympy/g2two_automorphism_order_ledger.py
python3 tools/sympy/g2_2_automorphism_theorem.py
python3 tools/sympy/split_octonion_g2_classification_evidence.py
python3 tools/sympy/finite_g22_atlas_vs_real_split.py
Singular -q tools/infra/g2two_split_zorn/g2two_split_zorn.sing
M2 --script tools/infra/g2two_split_zorn/g2two_split_zorn.m2
coqc tools/infra/g2two_split_zorn/coq/G2TwoSplitZorn.v
/home/goutev/Isabelle2025-2/bin/isabelle process_theories -l HOL -D tools/infra/g2two_split_zorn/isabelle G2TwoSplitZorn
echo G2TWO_SPLIT_ZORN_CANONICAL_MULTIENGINE_DONE
