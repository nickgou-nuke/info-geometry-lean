#!/usr/bin/env bash
set -euo pipefail
~/.elan/bin/lake build InfoGeometry.Lie.RealSplitOctonionG2Classification InfoGeometry.Canonical.SplitOctonionAutomorphism
~/.elan/bin/lake env lean lean/InfoGeometry/All.lean
python3 tools/sympy/split_octonion_derivation_classification.py
python3 tools/infra/real_split_g2_classification/real_split_g2_exact_ca.py
python3 tools/sympy/finite_g22_atlas_vs_real_split.py
/home/goutev/miniforge3/envs/sage/bin/sage tools/infra/real_split_g2_classification/real_split_g2_classification.sage.py
/home/goutev/miniforge3/envs/sage/bin/gap -q tools/infra/real_split_g2_classification/real_split_g2_classification.g
Singular -q tools/infra/real_split_g2_classification/real_split_g2_classification.sing
M2 --script tools/infra/real_split_g2_classification/real_split_g2_classification.m2
M2 --script tools/infra/real_split_g2_classification/real_split_g2_classification_dmodules.m2
coqc tools/infra/real_split_g2_classification/coq/RealSplitG2Classification.v
rm -f \
  tools/infra/real_split_g2_classification/coq/.RealSplitG2Classification.aux \
  tools/infra/real_split_g2_classification/coq/RealSplitG2Classification.glob \
  tools/infra/real_split_g2_classification/coq/RealSplitG2Classification.vo \
  tools/infra/real_split_g2_classification/coq/RealSplitG2Classification.vok \
  tools/infra/real_split_g2_classification/coq/RealSplitG2Classification.vos
/home/goutev/Isabelle2025-2/bin/isabelle process_theories -l HOL -D tools/infra/real_split_g2_classification/isabelle RealSplitG2Classification
echo REAL_SPLIT_G2_CLASSIFICATION_EVIDENCE_MULTIENGINE_DONE
