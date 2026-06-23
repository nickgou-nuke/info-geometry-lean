#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

echo "[smoke] building InfoGeometry.Projective.All"
lake build InfoGeometry.Projective.All

echo "[smoke] building InfoGeometry.Topology.All"
lake build InfoGeometry.Topology.All

if [[ "${STRICT_PROOF_SURFACE:-0}" == "1" ]]; then
  echo "[smoke] strict proof-surface scan"
  rg -n \
    "\\bsorry\\b|sorryProof|\\badmit\\b|\\baxiom\\b|∨ True|\\bor True\\b|Prop :=[[:space:]]*True|: True :=|_True|_valid|_certificate|_law|law_holds|recovery_law|Certificate|Witness|structure .*Bridge|structure .*Interface|certificate-shaped" \
    lean/InfoGeometry/Topology/GrandUnificationLinker.lean \
    lean/InfoGeometry/Topology/ThermodynamicGauge.lean \
    lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean \
    lean/InfoGeometry/Topology/BostConnesWilsonLoop.lean \
    lean/InfoGeometry/Projective/OnShellResidueBCFWBridge.lean \
    lean/InfoGeometry/Projective/MacaulayTrackBIngestion.lean
fi

echo "[smoke] import spikes passed"
