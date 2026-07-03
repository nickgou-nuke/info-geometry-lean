#!/usr/bin/env bash
set -euo pipefail
~/.elan/bin/lake env lean lean/InfoGeometry/Lie/SplitOctonion235Distribution.lean
python3 tools/infra/split_octonion_235_distribution/split_octonion_235_exact_ca.py
/home/goutev/miniforge3/envs/sage/bin/sage tools/infra/split_octonion_235_distribution/split_octonion_235.sage.py
/home/goutev/miniforge3/envs/sage/bin/gap -q tools/infra/split_octonion_235_distribution/split_octonion_235.g
/home/goutev/miniforge3/envs/sage/bin/Singular -q tools/infra/split_octonion_235_distribution/split_octonion_235.sing
M2 --script tools/infra/split_octonion_235_distribution/split_octonion_235.m2
M2 --script tools/infra/split_octonion_235_distribution/split_octonion_235_dmodules.m2
coqc tools/infra/split_octonion_235_distribution/coq/SplitOctonion235Distribution.v
rm -f \
  tools/infra/split_octonion_235_distribution/coq/.SplitOctonion235Distribution.aux \
  tools/infra/split_octonion_235_distribution/coq/SplitOctonion235Distribution.glob \
  tools/infra/split_octonion_235_distribution/coq/SplitOctonion235Distribution.vo \
  tools/infra/split_octonion_235_distribution/coq/SplitOctonion235Distribution.vok \
  tools/infra/split_octonion_235_distribution/coq/SplitOctonion235Distribution.vos
/home/goutev/Isabelle2025-2/bin/isabelle process_theories -l HOL -D tools/infra/split_octonion_235_distribution/isabelle SplitOctonion235Distribution
echo SPLIT_OCTONION_235_DISTRIBUTION_MULTIENGINE_DONE
