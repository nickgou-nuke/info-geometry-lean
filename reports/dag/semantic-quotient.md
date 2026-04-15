# Semantic Quotient

This report contracts presentation-duplicate packets, transport projections, and suspicious theorem-surface shells before reranking structural hotspots.
It is a heuristic quotient, not kernel truth.

## Summary
- structural hotspots analyzed: `13`
- top raw hotspot: `InfoGeometry.Krein.KreinSpace`
- top residual knot after contraction: `InfoGeometry.Krein.KreinSpace`
- top shell-heavy hotspot: `InfoGeometry.Canonical.RealBdGDIIIAtom`
- shell classes: `{'constructive_core': 8, 'mixed': 3, 'shell_heavy': 2}`
- contractible packet candidates: `10`

## Residual Knots
| Rank | Module | Raw | Residual | Shell | Class | Drivers |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `InfoGeometry.Krein.KreinSpace` | 43.6 | 43.6 | 0.00 | constructive_core | mostly retained after contraction |
| 2 | `InfoGeometry.Krein.DoubledSpace` | 25.9 | 25.9 | 0.00 | constructive_core | mostly retained after contraction |
| 3 | `InfoGeometry.Canonical.TomitaTakesaki` | 18.6 | 18.4 | 0.01 | constructive_core | mostly retained after contraction |
| 4 | `InfoGeometry.Krein.Superphysics` | 18.6 | 17.9 | 0.04 | constructive_core | mostly retained after contraction |
| 5 | `InfoGeometry.Canonical.SuperchargeCARCCRBridge` | 16.6 | 16.3 | 0.02 | constructive_core | mostly retained after contraction |
| 6 | `InfoGeometry.Canonical.RealBdGDIIIAtom` | 37.9 | 15.5 | 0.59 | mixed | packet duplication/projection, dedup family overlap |
| 7 | `InfoGeometry.Canonical.DIIICommutatorInitialization` | 8.6 | 7.9 | 0.08 | constructive_core | mostly retained after contraction |
| 8 | `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | 20.8 | 7.6 | 0.63 | mixed | packet duplication/projection, dedup family overlap |
| 9 | `InfoGeometry.Quantum.BulkBoundary` | 7.7 | 7.4 | 0.04 | constructive_core | mostly retained after contraction |
| 10 | `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | 20.8 | 6.7 | 0.68 | shell_heavy | theorem-surface shell, packet duplication/projection, dedup family overlap |
| 11 | `InfoGeometry.Canonical.RealBdG` | 6.6 | 6.6 | 0.00 | constructive_core | mostly retained after contraction |
| 12 | `InfoGeometry.Canonical.ModularSuperchargeClosure` | 6.8 | 2.9 | 0.57 | mixed | packet duplication/projection, dedup family overlap |
| 13 | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | 8.2 | 1.7 | 0.79 | shell_heavy | theorem-surface shell, packet duplication/projection, dedup family overlap |

## Shell-Heavy Hotspots
| Module | Raw | Residual | Theorem shell | Packet shell | Dedup | Top witness |
| --- | --- | --- | --- | --- | --- | --- |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | 37.9 | 15.5 | 0.19 | 0.99 | 112.7 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | 20.8 | 6.7 | 0.35 | 1.00 | 101.2 | `InfoGeometry.Canonical.InverseKernel` |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | 20.8 | 7.6 | 0.27 | 1.00 | 101.2 | `InfoGeometry.Krein.KreinSpace` |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | 8.2 | 1.7 | 0.59 | 0.99 | 10.8 | `InfoGeometry.Canonical.Drazin.IsDrazinInverse` |
| `InfoGeometry.Canonical.ModularSuperchargeClosure` | 6.8 | 2.9 | 0.14 | 1.00 | 101.2 | `InfoGeometry.Canonical.InverseKernel` |
| `InfoGeometry.Canonical.DIIICommutatorInitialization` | 8.6 | 7.9 | 0.17 | 0.00 | 0.0 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Krein.Superphysics` | 18.6 | 17.9 | 0.07 | 0.00 | 0.0 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Canonical.SuperchargeCARCCRBridge` | 16.6 | 16.3 | 0.04 | 0.00 | 0.0 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Quantum.BulkBoundary` | 7.7 | 7.4 | 0.09 | 0.00 | 0.0 | `InfoGeometry.Quantum.BulkBoundary.EndS` |
| `InfoGeometry.Canonical.TomitaTakesaki` | 18.6 | 18.4 | 0.02 | 0.00 | 0.0 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Canonical.RealBdG` | 6.6 | 6.6 | 0.00 | 0.00 | 0.0 | `InfoGeometry.Krein.InvolutiveSelfDualCarrier` |
| `InfoGeometry.Krein.DoubledSpace` | 25.9 | 25.9 | 0.00 | 0.00 | 0.0 | `InfoGeometry.Krein.DoubledSpace` |
| `InfoGeometry.Krein.KreinSpace` | 43.6 | 43.6 | 0.00 | 0.00 | 0.0 | `InfoGeometry.Krein.instL2Complete` |

## Contractible Packet Candidates
| Module | Packet | Kind | Endpoint | Mass | Why |
| --- | --- | --- | --- | --- | --- |
| `InfoGeometry.Canonical.ModularSuperchargeClosure` | `packet:4a144b4c0ba5` | presentation_duplicate | `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | 79.2 | presentation_duplicate, wrappers:11, hypothesis_endpoint |
| `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | `packet:4a144b4c0ba5` | presentation_duplicate | `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | 79.2 | presentation_duplicate, wrappers:11, hypothesis_endpoint |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | `packet:4a144b4c0ba5` | presentation_duplicate | `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | 79.2 | presentation_duplicate, wrappers:11, hypothesis_endpoint |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | `packet:4a144b4c0ba5` | presentation_duplicate | `InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` | 79.2 | presentation_duplicate, wrappers:11, hypothesis_endpoint |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | `packet:7ecf881177c6` | presentation_duplicate | `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_laws` | 16.4 | presentation_duplicate, wrappers:1, package_endpoint |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | `packet:c61b117fcc09` | presentation_duplicate | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode` | 7.8 | presentation_duplicate, wrappers:1, surrogate_endpoint |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | `packet:51bbf7af4558` | transport_projection | `InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_topologicalClassDIII_of_realBdGDatum` | 6.0 | transport_projection, package_endpoint |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | `packet:e406b05dd1a5` | single_strand | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` | 0.7 | surrogate_endpoint |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | `packet:b8801bfb9530` | single_strand | `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` | 0.7 | package_endpoint |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | `packet:f9c8c0ea2878` | single_strand | `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace` | 0.5 | package_endpoint |

## Method
- theorem-surface shell uses weighted suspicious theorem categories from `theorem-surface-index.json`
- packet shell contracts `presentation_duplicate` packets by default and discounts `transport_projection` packets
- dedup families contribute extra shell pressure where a hotspot still carries exact repeated sink surfaces
- residual score = raw structural score after removing the estimated shell ratio
