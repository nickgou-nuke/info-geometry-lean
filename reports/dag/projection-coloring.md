# Projection Coloring

This report clusters the lower constructive/source side of the maintained source-sink graph and projects those cluster colors upward onto carrier and sink modules.
It is a maintained heuristic over the authoritative DAG artifacts, not kernel truth.

## Summary
- source modules clustered: `8`
- lower clusters: `2`
- active affinity edges: `6` at threshold `0.80`
- top sink projection: `InfoGeometry.Canonical.RealBdGDIIIAtom`
- top carrier projection: `InfoGeometry.Canonical.RealBdGDIIIAtom`
- monochrome shell candidates: `5`
- braided sink modules: `0`

## Lower Clusters
| Cluster | Members | Top Direct Targets | Top Sink Families | Mass |
| --- | --- | --- | --- | --- |
| `cluster:0182dc1b20` | `DIIICommutatorInitialization`, `RealBdG`, `SuperchargeCARCCRBridge`, `TomitaTakesaki`, `DoubledSpace`, `KreinSpace`, `Superphysics` | `RealBdGDIIIAtom`:42.0, `DoubledSpace`:39.5, `SuperchargeCARCCRBridge`:29.0 | `RealBdGDIIIAtom`:40.0, `ModularSuperchargeClosure`:9.0, `UnifiedSuperchargeAlgebra`:8.0 | 220.5 |
| `cluster:6e6cf9d149` | `BulkBoundary` | `BulkBoundaryRegularizationBridge`:28.0 | `BulkBoundaryRegularizationBridge`:26.0 | 28.0 |

## Monochrome Shell Candidates
| Module | Shell | Dominant Cluster | Share | Cluster Members |
| --- | --- | --- | --- | --- |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | mixed | `cluster:0182dc1b20` | 1.00 | `DIIICommutatorInitialization`, `RealBdG`, `SuperchargeCARCCRBridge`, `TomitaTakesaki` |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | shell_heavy | `cluster:6e6cf9d149` | 1.00 | `BulkBoundary` |
| `InfoGeometry.Canonical.ModularSuperchargeClosure` | mixed | `cluster:0182dc1b20` | 1.00 | `DIIICommutatorInitialization`, `RealBdG`, `SuperchargeCARCCRBridge`, `TomitaTakesaki` |
| `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | shell_heavy | `cluster:0182dc1b20` | 1.00 | `DIIICommutatorInitialization`, `RealBdG`, `SuperchargeCARCCRBridge`, `TomitaTakesaki` |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | mixed | `cluster:0182dc1b20` | 1.00 | `DIIICommutatorInitialization`, `RealBdG`, `SuperchargeCARCCRBridge`, `TomitaTakesaki` |

## Braided Sink Modules
| Module | Clusters | Top Share | Mass | Cluster Mix |
| --- | --- | --- | --- | --- |
| - | - | - | - | - |

## Top Sink Projections
| Module | Class | Dominant Cluster | Share | Clusters | Mass |
| --- | --- | --- | --- | --- | --- |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | monochrome | `cluster:0182dc1b20` | 1.00 | 1 | 40.0 |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | monochrome | `cluster:6e6cf9d149` | 1.00 | 1 | 26.0 |
| `InfoGeometry.Canonical.ModularSuperchargeClosure` | monochrome | `cluster:0182dc1b20` | 1.00 | 1 | 9.0 |
| `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | monochrome | `cluster:0182dc1b20` | 1.00 | 1 | 8.0 |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | monochrome | `cluster:0182dc1b20` | 1.00 | 1 | 8.0 |

## Method
- lower/source modules come from `hydrated_edges[*].source_module` in `source-sink-bipartite.json`
- source affinity combines direct source-to-source chains, co-target overlap, and maintained fiber / entanglement group evidence
- clusters are connected components after thresholding the affinity graph
- colors are projected upward to sink modules using `incidence_entries` and to carrier modules using `hydrated_edges`
- `monochrome` means one lower cluster dominates; `braided` means the sink is genuinely mixed across lower clusters
