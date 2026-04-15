# OpenClaw Target Selector

This report selects operational targets from graph coverage first and native structural hotspots second.

## Source Summary
- declaration nodes: `17372`
- SCC components: `17372`
- layers: `31`
- roots: `722`
- capstones: `6627`
- structural active carriers: `13`
- structural top selector score: `43.65`
- declaration-index files: `615` / declaration-bearing source files `617`
- import-only / umbrella Lean files: `77`
- missing declaration-bearing files from graph coverage: `2`
- debt files outside graph coverage: `0`

## Primary Target
- `InfoGeometry.Krein.KreinSpace` from `structural_hotspot` | score `43.65` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `0` | corridor-reuse `26`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.instL2Complete`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.instL2Complete" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.json" --frontier-index 0 --fresh-worktree`

## Uncovered Debt Targets
- none

## Structural Hotspot Targets
- `InfoGeometry.Krein.KreinSpace` | score `43.65` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `0` | corridor-reuse `26`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.instL2Complete`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.instL2Complete" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-instl2complete.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.RealBdGDIIIAtom` | score `37.9` | bleed-src `1` | bleed-tgt `0` | missing `1` | dom-pressure `1` | corridor-reuse `15`
- anchor-status: `unanchored`
- seed: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.InvolutiveSelfDualCarrier" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Krein.DoubledSpace` | score `25.9` | bleed-src `0` | bleed-tgt `2` | missing `0` | dom-pressure `0` | corridor-reuse `15`
- anchor-status: `anchored`
- seed: `InfoGeometry.Krein.DoubledSpace`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.DoubledSpace" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-doubledspace.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-doubledspace.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-doubledspace.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | score `20.8` | bleed-src `1` | bleed-tgt `0` | missing `2` | dom-pressure `0` | corridor-reuse `4`
- anchor-status: `unanchored`
- seed: `InfoGeometry.Canonical.InverseKernel`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Canonical.InverseKernel" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | score `20.8` | bleed-src `1` | bleed-tgt `0` | missing `2` | dom-pressure `0` | corridor-reuse `4`
- anchor-status: `unanchored`
- seed: `InfoGeometry.Krein.KreinSpace`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.KreinSpace" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-kreinspace.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-kreinspace.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-kreinspace.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.TomitaTakesaki` | score `18.6` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `1` | corridor-reuse `10`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.InvolutiveSelfDualCarrier" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Krein.Superphysics` | score `18.6` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `1` | corridor-reuse `10`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.InvolutiveSelfDualCarrier" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.SuperchargeCARCCRBridge` | score `16.6` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `0` | corridor-reuse `10`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.InvolutiveSelfDualCarrier" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.DIIICommutatorInitialization` | score `8.6` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `1` | corridor-reuse `4`
- anchor-status: `strictly_safe`
- seed: `InfoGeometry.Krein.InvolutiveSelfDualCarrier`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Krein.InvolutiveSelfDualCarrier" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-krein-involutiveselfdualcarrier.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | score `8.2` | bleed-src `0` | bleed-tgt `1` | missing `0` | dom-pressure `0` | corridor-reuse `4`
- anchor-status: `anchored`
- seed: `InfoGeometry.Canonical.Drazin.IsDrazinInverse`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Canonical.Drazin.IsDrazinInverse" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-drazin-isdrazininverse.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-drazin-isdrazininverse.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-drazin-isdrazininverse.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Quantum.BulkBoundary` | score `7.7` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `0` | corridor-reuse `4`
- anchor-status: `anchored`
- seed: `InfoGeometry.Quantum.BulkBoundary.EndS`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Quantum.BulkBoundary.EndS" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-quantum-bulkboundary-ends.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-quantum-bulkboundary-ends.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-quantum-bulkboundary-ends.json" --frontier-index 0 --fresh-worktree`
- `InfoGeometry.Canonical.ModularSuperchargeClosure` | score `6.85` | bleed-src `0` | bleed-tgt `0` | missing `0` | dom-pressure `0` | corridor-reuse `4`
- anchor-status: `unanchored`
- seed: `InfoGeometry.Canonical.InverseKernel`
- skynet: `python3 tools/skynet_v2.py --seed "InfoGeometry.Canonical.InverseKernel" --walk reverse --json-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.json" --md-out "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.md"`
- optimization: `python3 tools/run_optimization_cycle.py --frontier-json "reports/dag/skynet-v2-frontier-structural-hotspot-infogeometry-canonical-inversekernel.json" --frontier-index 0 --fresh-worktree`
