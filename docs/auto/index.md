# InfoGeometry Auto Status

Status:
- generated from local repository state and trusted DAG artifacts
- authoritative for current metrics/frontier snapshot
- preferred refresh path: `python3 tools/update_repo_docs.py`
- low-level generator: `python3 tools/generate_auto_docs.py`

## Repository Scale
- Lean files under `lean/`: **444**
- Lean LOC under `lean/`: **74,391**

## Trusted Semantic Exports
| Module | Semantic nodes | Semantic edges | Skeleton nodes | Top hubs |
| :--- | ---: | ---: | ---: | :--- |
| `KasparovCycle` | 7 | 26 | 4 | `InfoGeometry.KK.EndH`, `InfoGeometry.KK.IsCompactEnd`, `InfoGeometry.KK.KasparovCycle` |
| `AnalyticalIndex` | 59 | 209 | 42 | `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus`, `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus`, `InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus` |
| `OperatorAlgebraBridge` | 6 | 3 | 2 | `InfoGeometry.Canonical.OperatorAlgebraBridge.IsCStarLayer`, `InfoGeometry.Canonical.OperatorAlgebraBridge.IsCompleteCStarLayer` |
| `GrandSynthesis` | 56 | 90 | 30 | `InfoGeometry.Canonical.GrandSynthesis.bochnerWeitzenboeckBridge_of_ibDynamics`, `InfoGeometry.Canonical.GrandSynthesis.kahlerPotentialRN`, `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_implication_of_ibDynamics_and_indexHypotheses` |

## Verified Bridge Snapshot
- seed declaration: `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- seed block: `block:2093-2449`
- direct hard dependency detected: `InfoGeometry.KK.KasparovCycle.analyticalIndex -> InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`

## Skynet v2 Frontier
- graph nodes: **128**
- graph edges: **647**
- cross-module edges: **319**
- seed blocks: **1**

### Local Bridge Kernel (`--walk both`)
- `InfoGeometry.KK.KasparovCycle`
- `InfoGeometry.KK.index_bridge_spectral`
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
- `InfoGeometry.KK.superComm_compact_of_even_rep`
- `InfoGeometry.KK.comm_compact_lie`
- `InfoGeometry.KK.EndH`

### Downstream Consumer Frontier (`--walk reverse`)
- `InfoGeometry.KK.index_bridge_spectral`
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
- `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_conjugacy`
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_conjugacy`
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_gap`

### First GrandSynthesis Consumer Hits
- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses`
- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_fullCapstone`

## Current Reading Order
1. `README.md`
2. `lean/DAG/README.md`
3. `skills/info-geometry-repo/references/frontier-prompt.md`
4. `skills/info-geometry-repo/references/bridge-candidates.md`

## Notes
- This page is a generated status view, not a narrative design document.
- Generated DAG JSONs under `reports/dag/` are intentionally untracked.
- Historical crosswalk/intake documents may still exist, but this page reflects the current trusted bridge workflow.

