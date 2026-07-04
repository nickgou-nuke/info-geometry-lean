#!/usr/bin/env bash
set -euo pipefail

lake env lean lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean
python3 tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis.py
/home/goutev/miniforge3/envs/sage/bin/python tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis.sage.py
gap -q tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis.g
Singular -q tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis.sing
M2 --script tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis.m2
M2 --script tools/infra/primon_crystallization_synthesis/primon_crystallization_synthesis_dmodules.m2
coqc tools/infra/primon_crystallization_synthesis/coq/PrimonCrystallizationSynthesis.v
rm -f tools/infra/primon_crystallization_synthesis/coq/.PrimonCrystallizationSynthesis.aux \
      tools/infra/primon_crystallization_synthesis/coq/PrimonCrystallizationSynthesis.vo \
      tools/infra/primon_crystallization_synthesis/coq/PrimonCrystallizationSynthesis.vos \
      tools/infra/primon_crystallization_synthesis/coq/PrimonCrystallizationSynthesis.vok \
      tools/infra/primon_crystallization_synthesis/coq/PrimonCrystallizationSynthesis.glob
/home/goutev/Isabelle2025-2/bin/isabelle build -D tools/infra/primon_crystallization_synthesis/isabelle

echo PRIMON_CRYSTALLIZATION_SYNTHESIS_MULTIENGINE_DONE
