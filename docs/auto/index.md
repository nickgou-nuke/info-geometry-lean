# InfoGeometry Auto Status

Status:
- generated from local repository state and trusted DAG artifacts
- authoritative for current metrics/frontier snapshot
- preferred refresh path: `python3 tools/docs/update_repo_docs.py`
- low-level generator: `python3 tools/docs/generate_auto_docs.py`
- declaration-level causal-order inputs live under `artifacts/dag/`; derived frontier/causal reports and NetworkX exports live under `reports/dag/`

## Repository Scale
- Lean files under `lean/`: **467**
- Lean LOC under `lean/`: **81,615**

## Trusted Semantic Exports
| Module | Semantic nodes | Semantic edges | Skeleton nodes | Top hubs |
| :--- | ---: | ---: | ---: | :--- |
| `KasparovCycle` | 7 | 26 | 4 | `InfoGeometry.KK.EndH`, `InfoGeometry.KK.IsCompactEnd`, `InfoGeometry.KK.KasparovCycle` |
| `AnalyticalIndex` | 59 | 209 | 42 | `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus`, `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus`, `InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus` |
| `OperatorAlgebraBridge` | 11 | 19 | 3 | `InfoGeometry.Canonical.OperatorAlgebraBridge.IsCStarLayer`, `InfoGeometry.Canonical.OperatorAlgebraBridge.IsCompleteCStarLayer`, `InfoGeometry.Canonical.OperatorAlgebraBridge.cstar_completeCStar_kms_fock_package` |
| `GrandSynthesis` | 67 | 94 | 31 | `InfoGeometry.Canonical.GrandSynthesis.bochnerWeitzenboeckBridge_of_ibDynamics`, `InfoGeometry.Canonical.GrandSynthesis.RNEntropySourcesMongeAmpere`, `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_implication_of_ibDynamics_and_indexHypotheses` |

## Verified Bridge Snapshot
- seed declaration: `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- seed block: `block:2093-2449`
- direct hard dependency detected: `InfoGeometry.KK.KasparovCycle.analyticalIndex -> InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`

## Skynet v2 Frontier
- graph nodes: **1366**
- graph edges: **11707**
- cross-module edges: **6365**
- seed blocks: **1**

### Local Bridge Kernel (`--walk both`)
- `InfoGeometry.KK.KasparovCycle`
- `KreinGradedModule`
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
- `InfoGeometry.KK.index_bridge_spectral`
- `KreinGradedModule.gradeCLM`
- `InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit`

### Downstream Consumer Frontier (`--walk reverse`)
- `InfoGeometry.KK.index_bridge_spectral`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete`
- `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel`
- `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_boundaryLocalization`

### First GrandSynthesis Consumer Hits
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`

## Current Reading Order
1. `README.md`
2. `lean/DAG/README.md`
3. `tools/README.md`
4. `skills/info-geometry-repo/references/frontier-prompt.md`
5. `skills/info-geometry-repo/references/bridge-candidates.md`

## Notes
- This page is a generated status view, not a narrative design document.
- Trusted declaration graph inputs for causal-order analysis live under `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`.
- NetworkX-readable graph outputs live under `reports/dag/declaration-networkx.graphml`, `reports/dag/module-networkx.graphml`, `reports/dag/module-networkx.svg`, and the filtered frontier siblings `*-frontier.graphml` / `*-frontier.svg`.
- Treat causal-order rankings as provisional until `reports/dag/true-root-order.md` shows no coverage warning; the public `artifacts/dag/` graph may still be partial if `InfoGeometry.All` omits declaration-bearing branches.
- Use `reports/dag/missing-all-classification.md` to classify the remaining declaration-bearing files outside `InfoGeometry.All` into direct imports, branch-façade expansions, namespace fixes, and noncanonical exclusions.
- Generated semantic exports and derived frontier/causal JSONs under `reports/dag/` are intentionally untracked.
- Historical crosswalk/intake documents may still exist, but this page reflects the current trusted bridge workflow.

