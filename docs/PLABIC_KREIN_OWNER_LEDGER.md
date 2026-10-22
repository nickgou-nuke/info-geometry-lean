# Plabic/Krein owner ledger

This ledger maps the extracted archetypes to declaration-qualified repository
owners. It is an audit index, not a theorem certificate. A row is promoted only
when the named declaration exists in the checked-out Lean source; prose labels
and chat summaries do not create edges.

## Core owners

| Archetype | Qualified declarations | Source |
|---|---|---|
| A0 finite bipartite graph | `InfoGeometry.Canonical.FinitePlabicKasteleyn.FinitePlabicGraph` | `lean/InfoGeometry/Canonical/FinitePlabicKasteleyn.lean:28` |
| A1 Kasteleyn signing | `InfoGeometry.Canonical.FinitePlabicKasteleyn.KasteleynSigning` | `lean/InfoGeometry/Canonical/FinitePlabicKasteleyn.lean:54` |
| A2 signed incidence matrix | `InfoGeometry.Canonical.FinitePlabicKasteleyn.edgeSumMatrix`, `edgeSumMatrix_add` | `lean/InfoGeometry/Canonical/FinitePlabicKasteleyn.lean:66,79` |
| A3 directed paths | `InfoGeometry.Topology.ChiralDirectedGraphHomotopy.DirectedPath`, `append`, `append_assoc` | `lean/InfoGeometry/Topology/ChiralDirectedGraphHomotopy.lean:40,44,66` |
| A4 presented path quotient | `DirectedPathPresentation`, `PresentedPathHomotopy`, `DirectedPathClass.comp` | `lean/InfoGeometry/Topology/ChiralDirectedGraphHomotopy.lean:585,607,233` |
| A6 block Dirac | `InfoGeometry.Canonical.PlabicDiracKrein.diracDHK` | `lean/InfoGeometry/Canonical/PlabicDiracKrein.lean:26` |
| A7 chiral grading | `kreinSignature`, `diracDHK_anticommutes_chirality` | `lean/InfoGeometry/Canonical/PlabicDiracKrein.lean:15,42` |
| A8 block square | `diracDHK_sq`, `edgeSumDirac_sq` | `lean/InfoGeometry/Canonical/PlabicDiracKrein.lean:32`; `lean/InfoGeometry/Canonical/FinitePlabicKasteleyn.lean:118` |
| A9 Krein skew relation | `diracDHK_krein_skew` | `lean/InfoGeometry/Canonical/PlabicDiracKrein.lean:49` |
| A11 nilpotent local matrix | `Cl11Op.edgeTwist`, `edgeTwist_sq_zero` | `lean/InfoGeometry/Holography/PlabicKreinTwistedClusterMutation.lean` |
| A12 unipotent transport | `edgeTransport`, `edgeTransportInv`, `edgeTransport_mul_inv`, `edgeTransportInv_mul` | `lean/InfoGeometry/Holography/PlabicKreinTwistedClusterMutation.lean` |
| A13 local conjugation / characteristic polynomial | `edgeTransport_conjugation_nodeBlack`, `matrix_edgeTransport_charpoly_invariant` | `lean/InfoGeometry/Holography/PlabicKreinTwistedClusterMutation.lean`; `lean/InfoGeometry/Holography/PlabicKreinMatrixBridge.lean` |
| A14 bridge/minor calculus | `addBridge`, `minor2_addBridge_right`, `minor2_addBridge_left` | `lean/InfoGeometry/Topology/PlabicBoundaryMeasurement.lean:21,34,43` |
| A15 Plücker carrier | `boundaryMeasurementMatrix`, `boundaryMeasurement_plucker_relation`, `boundaryMeasurement_totally_positive` | `lean/InfoGeometry/Topology/PlabicBoundaryMeasurement.lean:70,108,122` |
| A16 face mutation | `mutateF`, `mutateF_rev`, `cluster_mutation_involution`, `ptolemy_face_weight_add_one` | `lean/InfoGeometry/Topology/PlabicCluster.lean:28,41,146,185` |
| A17 thermodynamic graph | `DirectedThermoGraph`, `stochasticCurrent`, `circuitCurrent` | `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean:63,81,85` |
| A19 Wilson/path readouts | `pathForwardBackwardRatio_eq_exp_pathEntropyProduction`, `wilsonLoop_eq_exp_cycleCurvatureLog` | `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean:494,551` |
| A20 detailed balance | `detailedBalance_iff_all_cycle_wilsonLoop_eq_one`, `detailedBalance_iff_zero_log_curvature` | `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean:312,339` |
| A21 MaxCal law | `GraphMaxCalPathLaw`, `forward_backward_ratio_eq_exp_pathEntropy` | `lean/InfoGeometry/Canonical/MaximumCaliberPath.lean:45,69` |
| A24 operator contract | `NeuralOperator`, `NeuralOperatorApproximationContract`, `operator_totalCost_le_of_contract` | `lean/InfoGeometry/Canonical/NeuralOperatorCore.lean:20,63,86` |
| A25 modular-velocity bridge | `modularVelocityOperator_apply`, `modularVelocityOperator_totalCost_le_of_contract`, `modularVelocityOperator_readoutError_le_of_contract` | `lean/InfoGeometry/Canonical/NavierStokesNeuralOperatorBridge.lean:45,77,96` |
| A26 sheet transfers | `upward`, `downward`, `upward_comp_upward`, `downward_comp_downward`, `pairedGenerator_sq` | `lean/InfoGeometry/Canonical/NavierStokesPolarizedTransfers.lean:26,30,43,49,84` |
| A27 legacy diagnostic | `legacy_backwardWave_eq_zero` | `lean/InfoGeometry/Canonical/NavierStokesPolarizedTransfers.lean:97` |

## Extracted C-archetype owner families

| C range | Source-qualified owner family | Scope decision |
|---|---|---|
| C0 | `InfoGeometry.Epistemology.ArchetypeHomotopyFramework`, `EpistemicFunctor`, `Meta.EpistemicCompiler` | Evidence scheduling only; not proof of chat claims. |
| C1 | `InfoGeometry.Algebra.Grothendieck`, `Canonical.TensorTowerColimit`, `Canonical.CategoricalColimitContinuumBridge` | Colimit/quotient claims remain owner-scoped. |
| C2–C3 | `InfoGeometry.Algebra.SuperGrassmannianClifford`, `Algebraic.JordanCliffordLieSplit` | Finite graded algebra only. |
| C4 | `InfoGeometry.Algebra.QDeformedJordanLieBridgeWave21.ScalarQCommutes`, `jordan_lie_balance_of_scalarQCommutes` | Scalar q-balance only. |
| C5 | `InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra`, `HyperrotorKMSBridge` | Local split/Bogoliubov identities only. |
| C6 | `InfoGeometry.Canonical.FiniteParaKahler`, `InfoGeometry.Algebra.KreinPosNegDecomposition` | Projectors/isotropy; no topology promotion. |
| C7 | `InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms`, `OnsagerOperatorClosure` | Conditional BKM/Onsager scope. |
| C8–C9 | `InfoGeometry.Geometry.ConstructiveKasparov`, `InfoGeometry.Algebra.WittProjectiveClosureHonest` | Finite/index/projective carriers only. |
| C10 | `InfoGeometry.Algebra.KleinBottleParabolicEmbedding`, `KleinBottleTwistedCommutantBridge` | Algebraic shadow only. |
| C11 | `InfoGeometry.Algebra.MadelungLogDensityCalculus` | Local log-density identities only. |
| C12 | `InfoGeometry.Canonical.NavierStokesPolarizedTransfers` | Linear transfer identities only. |
| C13 | `InfoGeometry.Algebra.SplitOctonionZornAlgebra`, `InfoGeometry.Algebra.Zorn.Basic` | Explicit nonassociative carrier only. |
| C14 | `InfoGeometry.Canonical.NeuralOperatorCore` | Contract-bound approximation only. |
| C15 | owners A0–A16 above | Local Plabic/Krein facts; bridges remain open. |
| C16 | owners A17–A22 above | Finite path/Wilson/MaxCal facts; optimizer existence is not inferred. |
| C17 | `InfoGeometry.Topology.ChiralDirectedGraphHomotopy`, `InfoGeometry.Epistemology.ArchetypeHomotopyFramework` | Open typed comparison edge; no semantic equivalence asserted. |

## Audit boundary

The live share URL was not independently re-fetched in this audit because the
browser-harness daemon socket was unavailable. The checked-in extraction is
validated for contiguous labels and immutable file hashes by
`tools/infra/validate_chatgpt_share_extraction.py`. The raw payload and decoder
are explicitly recorded as unavailable in the reproducibility manifest.
