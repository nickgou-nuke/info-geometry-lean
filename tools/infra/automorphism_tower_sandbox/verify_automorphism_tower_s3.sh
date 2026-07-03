#!/usr/bin/env bash
set -euo pipefail

lake env lean lean/InfoGeometry/GroupTheory/AutomorphismTower.lean
python3 tools/infra/automorphism_tower_sandbox/automorphism_tower_s3_exact.py
/home/goutev/miniforge3/envs/sage/bin/python tools/infra/automorphism_tower_sandbox/automorphism_tower_s3.sage.py
gap -q tools/infra/automorphism_tower_sandbox/automorphism_tower_s3.g
Singular -q tools/infra/automorphism_tower_sandbox/automorphism_tower_s3.sing
M2 --script tools/infra/automorphism_tower_sandbox/automorphism_tower_s3.m2
M2 --script tools/infra/automorphism_tower_sandbox/automorphism_tower_s3_dmodules.m2
coqc tools/infra/automorphism_tower_sandbox/coq/AutomorphismTowerS3.v
rm -f tools/infra/automorphism_tower_sandbox/coq/.AutomorphismTowerS3.aux \
      tools/infra/automorphism_tower_sandbox/coq/AutomorphismTowerS3.vo \
      tools/infra/automorphism_tower_sandbox/coq/AutomorphismTowerS3.vos \
      tools/infra/automorphism_tower_sandbox/coq/AutomorphismTowerS3.vok \
      tools/infra/automorphism_tower_sandbox/coq/AutomorphismTowerS3.glob
/home/goutev/Isabelle2025-2/bin/isabelle build -D tools/infra/automorphism_tower_sandbox/isabelle

echo AUTOMORPHISM_TOWER_S3_MULTIENGINE_DONE
