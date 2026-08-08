# Chiral tau-Ideal Stability Certificate
**Generated**: 2026-06-16T11:40:41.808989+00:00
**Database**: `info_geometry`

## Graph Counts
| Collection | Count |
|---|---|
| lean_decls | 1075 |
| syntax_nodes | 35161 |
| references | 3272 |
| ast_child | 34395 |
| has_syntax | 766 |

## 4-Cell tau-Ideal Matrix
| Cell | Kind | Ref By | Deps |
|---|---|---|---|
| `chiral_kernel_is_left_tau_ideal` | None | 1 | 9 |
| `chiral_left_tau_ideal` | None | 1 | 10 |
| `chiral_right_kernel_tau_ideal` | theorem | 0 | 9 |
| `chiral_right_tau_ideal` | theorem | 0 | 10 |

## Vacuity Scan
- sorry/admit atoms: **0**

## Core Lemmas (Top 10)
| Lemma | Used By |
|---|---|
| `ChiralCausalCone.M2C` | 120 |
| `AlgebraicCuntzQuotient.CuntzAlg` | 77 |
| `AlgebraicCuntzQuotient.instSemiringCuntzAlg` | 74 |
| `AlgebraicCuntzQuotient.instAlgebraCuntzAlg` | 62 |
| `ChiralCausalCone.σMinus` | 59 |
| `ChiralCausalCone.σPlus` | 59 |
| `ChiralCausalCone.σ3c` | 42 |
| `AlgebraicCuntzQuotient.T` | 37 |
| `AlgebraicCuntzQuotient.S` | 37 |
| `SupergradedCuntzBdG.Z2Parity` | 36 |

## Key Module Inventory
| Module | Theorems | Defs |
|---|---|---|
| `B3PresentedGroup` | 1 | 0 |
| `BraidIdealDescent` | 3 | 0 |
| `ChiralB3PresentedBridge` | 6 | 1 |
| `ChiralCausalCone` | 22 | 1 |
| `ChiralTensorMatrixBridge` | 1 | 1 |
| `ChiralTensorRecoupling` | 11 | 1 |
| `ChiralTLDescent` | 5 | 1 |
| `JonesBraidB3` | 1 | 0 |
| `TLChain` | 2 | 0 |
| `YangBaxterQSwap` | 1 | 1 |
| `YangBaxterQuotientDescent` | 2 | 0 |

## Socket / Boundary Inventory
| Kind | Name |
|---|---|
| `def` | `BiquaternionKANnilpotent.BiquaternionKANnilpotent.exp_K_N` |
| `def` | `ChiralB3PresentedBridge.ChiralB3PresentedBridge.canonical_parameter_correspondence` |
| `def` | `ChiralCausalCone.ChiralCausalCone.chiral_CAR_pair` |
| `def` | `ChiralTensorMatrixBridge.ChiralTensorMatrixBridge.e_matrix` |
| `def` | `ChiralTensorRecoupling.ChiralTensorRecoupling.klein_classification` |
| `def` | `ChiralTLDescent.ChiralTLDescent.R_chiral` |
| `def` | `ColorCARStandardModel.ColorCARStandardModel.fureyGeneration` |
| `def` | `CStarCuntzTensorQuotient.CStarCuntzTensorQuotient.UniversalCStarCompletionSocket` |
| `def` | `MobiusWittenIndex.MobiusWittenIndex.chiralParity` |
| `def` | `SplitClifford.SplitClifford.carPair_matrix` |
| `def` | `SplitClifford.SplitClifford.Cl00` |
| `def` | `SplitClifford.SplitClifford.cl11_from_cl00_step` |
| `def` | `SplitClifford.SplitClifford.cl22_as_cl11_gTensor_cl11` |
| `def` | `SplitClifford.SplitClifford.cl22_from_cl11_step` |
| `def` | `SplitClifford.SplitClifford.cl33_from_cl22_step` |
| `def` | `SplitClifford.SplitClifford.Cl44` |
| `def` | `SplitClifford.SplitClifford.cl55_from_cl44_step` |
| `def` | `SplitClifford.SplitClifford.grandCanonicalExponent` |
| `def` | `SplitClifford.SplitClifford.IsPureBloch` |
| `def` | `SplitClifford.SplitClifford.rindlerBeta` |
| `def` | `SplitClifford.SplitClifford.scaledJordanC` |
| `def` | `SplitClifford.SplitClifford.scaledLieC` |
| `def` | `SplitClifford.SplitClifford.unruhTemperature` |
| `def` | `TrifactorGeometry.TrifactorGeometry.sectorBySquare` |
| `def` | `YangBaxterQSwap.YangBaxterQSwap.C_q` |

## Proof Complexity (AST Nodes)
| Cell | AST Nodes |
|---|---|
| `chiral_kernel_is_left_tau_ideal` | 71 |
| `chiral_left_tau_ideal` | 71 |
| `chiral_right_kernel_tau_ideal` | 71 |
| `chiral_right_tau_ideal` | 71 |

## Transitive Users (1 total)
- `ChiralTLDescent.chiral_relation_is_left_tau_ideal`

## Cross-Module Paths (ChiralTLDescent -> BraidIdealDescent)
| From | To | Len |
|---|---|---|
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.CrossMap` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.leftTarget` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.leftTarget` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.tauL` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.IsLeftTauIdeal` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.leftTarget._proof_1` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.CrossMap` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.tauL._proof_2` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.tauL._proof_1` | 5 |
| `ChiralTLDescent.chiral_kernel_is_left_tau_ideal` | `BraidIdealDescent.tauL._proof_1` | 5 |
