# R3 Specification: Cl(1,1)-Tensored Graded Towers, Atom Symmetry, Graded Chains, Coordinate-Less Invariance, and R1 Coupling

Status: `[qms_document_draft]` (M2.1, M2.2, and M2.3 Lean code verified; pending independent M2.3 Iteration 2 spec review/gate acceptance per `ALCHEMICAL_QMS_SOP.md` §5A)  
Document ID: `SPEC-R3-CLIFFORD-TOWERS`  
Version: `1.1`  
Date: `2026-11-18`  
Baseline Commit: `abd5826b3676fab6231c66b646ec1cc5aeed6732`  
Toolchain Fingerprint: `Lean v4.34.1`, `Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612`  
QMS Governing SOP: `docs/ALCHEMICAL_QMS_SOP.md` (`QMS-SOP-ALC-001` v4.1)  
Risk Classification: `R3/R4` (algebraic/categorical APIs, `DirectLimit` inductive towers, coordinate-less `CliffordAlgebra Q` invariance, and R3 ↔ R1 coupling; strictly separated by finite-stage / algebraic `DirectLimit` / discrete-topological scopes per QMS §3.5)  
Upstream Spec Sibling: `docs/R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md` (`SPEC-R1-NCG-DIFFGEOM`)

---

## 1. Scope, Requirement Mapping (`F3.1–F3.5`), and QMS §3.5 Language Control

### 1.1 Purpose

This specification fixes the canonical mathematical definitions, verified API surfaces, explicit hypotheses, scope boundaries, and R3 ↔ R1 coupling contracts for **Requirement R3** (*Reconcile `Cl(1,1)`-tensored graded towers, symmetry of the operator algebra geometry by the `Cl(1,1)` atom symmetry, and graded tensor chains, and characterize Clifford algebra symmetry-invariant geometry as an invariant, coordinate-less representation of Clifford algebra properties*) across Milestones **M2.1**, **M2.2**, and **M2.3** of `info-geometry-lean`. Specifically:

1. **`F3.1` (`M2.2`)**: Reconciles all three `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)` matrix bases (`cl11EquivMat`, `cl11StandardEquiv`, `cl11MatrixAlgEquiv`) plus `cl11MatrixRep` (`SplitQuaternion`), unifies `ℤ/2`-graded Morita theory (`Cl11GradedMorita`, `Cl11GradedTensorMorita`) with `ClTower A n` / `ClInf A` (`NoncommutativeCliffordColimitMassGapSynthesis`) and `Clsplit n` / `SplitCliffordInfinity` (`SplitCliffordDirectLimit`, `SplitCliffordHeadTailTower`, `SplitCliffordTowerUnification`), and reconciles unital `splitCliffordStep` / `diagEmbed` against non-unital `splitCliffordCornerStep` / `bottEmbed`.
2. **`F3.2` (`M2.2`)**: Packages the Klein four-group `V₄` atom symmetry across `Cl(1,1)` and `M₂(ℝ)` (`Cl11KleinFourAdjointRepresentation`), lifts it with Koszul signs to `evenOdd q11 ᵍ⊗[ℝ] 𝒜` (`Cl11GradedTensorMorita`), and propagates it through `Clsplit n`, `SplitCliffordInfinity`, `MatStage n`, and `DoubleCylinderColimit ℝ` (`SplitCliffordTowerUnification`, `ErlangenDoubleCylinderSymmetryInvariants`).
3. **`F3.3` (`M2.2`)**: Reconciles graded tensor chains (`Cl11HomogeneousChains`: `nativeChain`, `ordinaryChain`, `singleSiteChain`, `prefixParity`, `suffixParity`), resolves the `BondCoherence` obstruction (`SplitCliffordMatrixLimitSoldering`: `gradedTensorSuccessor_not_algHom` vs unconditional JW bit-word soldering `canonicalCliffordUHFColimitEquiv`), transports `jwDifferential` / `jwHomotopy` onto `SplitCliffordInfinity` and `nativeChain` (`Cl11GradedDifferential`), and connects exact and rank-minimal Clifford tensor trains (`Cl11TensorTrainSynthesis`).
4. **`F3.4` (`M2.1`)**: Establishes genuine basis-free `O(Q)` / `SO(Q)` / `IsometryEquiv` invariance on arbitrary `CliffordAlgebra Q` (`GradedGraceContraction`, `CoordinateLessCliffordInvariance`, `CliffordSymmetryLift`) grounded in Felix Klein's 1872 *Erlanger Programm* (`ABN7632.0001.001` / `arXiv:0807.3161v1`), while scoping `ErlangenCoordinateless.lean` honestly to concrete `M₂(ℂ)` Pauli spin-frame identities.
5. **`F3.5` (`M2.3`)**: Couples R3 graded exterior/Clifford Hodge–Dirac forms (`ZornDifferentialFormsCliffordBridge`: `FormHodgeCliffordData`, `equivExterior`-conjugated `chevalleyAction`, `cliffordMorphismPullbackForm`) and abstract `CliffordAlgebra Q` Cartan–Hestenes rotors, Darboux spin connections, and `Spin(Q)` conjugation (`CartanHestenesRotorSpinConnectionMaurerCartanSynthesis`) to R1's `DerivationExteriorCalculus` (`LieActionLane` / `DerivationLieLane`) and `MaurerCartanTower` (`thetaL`, `thetaR`, `ceCurvature`), while flagging `CliffordMobiusDeRhamMonodromy.lean` as `BUCKET 3`.

### 1.2 Requirement & Milestone Mapping (`PROJECT.md` & `SCOPE.md`)

| Feature | Summary | Sub-Milestone | Primary Lean Owner(s) |
|---|---|---|---|
| **F3.1** | `Cl(1,1)` 3-basis reconciliation, `ℤ/2`-graded Morita & `evenOdd q11 ᵍ⊗[ℝ] 𝒜`, Lane 1 ↔ Lane 3 towers (`Clsplit n`/`SplitCliffordInfinity` ↔ `ClTower A n`/`ClInf A`), `diagEmbed`/`bottEmbed` reconciliation | **M2.2** | `Clifford/Cl11Matrix.lean`, `Clifford/Cl11GradedMorita.lean`, `Clifford/Cl11GradedTensorMorita.lean`, `Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean`, `Canonical/SplitCliffordDirectLimit.lean`, `Canonical/SplitCliffordHeadTailTower.lean`, `Canonical/SplitCliffordTowerUnification.lean`, `Topology/SplitCliffordHeisenbergTopological.lean`, `Clifford/CliffordTower.lean` |
| **F3.2** | `Cl(1,1)` `V₄` atom symmetry (`localCl11Map`, `cl11V4SymmetryAction`, `headLiftSymmetryAction`), Koszul-sign intertwining, tower & `DoubleCylinderColimit ℝ` propagation (`doubleCylinderColimitV4_restrict_gSwap`) | **M2.2** | `Canonical/Cl11KleinFourAdjointRepresentation.lean`, `Clifford/Cl11GradedTensorMorita.lean`, `Canonical/SplitCliffordTowerUnification.lean`, `OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean` |
| **F3.3** | Graded tensor chains (`nativeChain`, `ordinaryChain`, `singleSiteChain`, `prefixParity`/`suffixParity`), `BondCoherence` falsity (`gradedTensorSuccessor_not_algHom`) vs JW soldering, `splitJWDifferential` / `nativeChainDifferential` / `Fin.rev` duality, exact/minimal Clifford tensor trains | **M2.2** | `Clifford/Cl11HomogeneousChains.lean`, `Clifford/Cl11GradedDifferential.lean`, `Canonical/SplitCliffordMatrixLimitSoldering.lean`, `Clifford/Cl11TensorTowerLimit.lean`, `Clifford/Cl11TensorTrainSynthesis.lean` |
| **F3.4** | Coordinate-less `CliffordAlgebra.equivOfIsometry` commutation (`involute`, `reverse`, `evenOdd`, `cliffordGradeProj`, `hTrace_cl`, `cliffordKreinPairing`, `graceOperator`), `SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q)`, `O(Q)`/`SO(Q)`/`V₄` invariant characterization, `ErlangenCoordinateless` `M₂(ℂ)` alignment | **M2.1** | `Clifford/GradedGraceContraction.lean`, `Clifford/CoordinateLessCliffordInvariance.lean`, `Algebraic/CliffordSymmetryLift.lean`, `ErlangenCoordinateless.lean`, `Clifford/SplitClifford55ExteriorFiniteGraded.lean` |
| **F3.5** | R3 ↔ R1 coupling (`FormHodgeCliffordData` ↔ `cliffordGradeProj`/`equivExterior`, faithful `chevalleyAction`, `cliffordMorphismPullbackForm`), abstract `CliffordAlgebra Q` rotor/Darboux/`MaurerCartanTower` (`thetaR`/`thetaL`), `spinGroupToIsometryHom`, `Cl(1,1)` boost rotor, R3 Spec (`BUCKET 3` `CliffordMobiusDeRhamMonodromy.lean`) | **M2.3** | `Canonical/ZornDifferentialFormsCliffordBridge.lean`, `Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean`, `docs/R3_CLIFFORD_TOWERS_AND_INVARIANCE_SPEC.md`, (`Topology/CliffordMobiusDeRhamMonodromy.lean` `BUCKET 3`) |

### 1.3 QMS §3.5 Colimit & Staged-System Language Control

Per `docs/ALCHEMICAL_QMS_SOP.md` §3.5, every R3 claim carries one of the approved exact scopes below; standalone `"infinite"`, `"thermodynamic limit"`, `"continuum limit"`, or `"global colimit"` are prohibited outside explicit `non_theorem_claims` or `BUCKET 3` rejections naming the missing owner structure:

| Scope Tag | Mathematical Meaning in R3 | Representative Lean Owners |
|---|---|---|
| `finite stage` | Single fixed `n : ℕ` or fixed finite-dimensional `(M, Q)` | `Cl11Matrix`, `Cl11GradedMorita`, `Cl11GradedTensorMorita`, `Cl11HomogeneousChains`, `Cl11TensorTrainSynthesis`, `GradedGraceContraction`, `CoordinateLessCliffordInvariance`, `ZornDifferentialFormsCliffordBridge`, `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis` |
| `staged theorem transported by explicit successor maps` | Transported step-by-step along explicit `n ↦ n + 1` maps | `SplitCliffordDirectLimit` (`splitCliffordStep`), `SplitCliffordHeadTailTower` (`splitCliffordHeadTailStep`), `SplitCliffordTowerUnification` (`clSplitGradedTensorEquivClTower`, `diagV4ClsplitAuto_bond`), `SplitCliffordMatrixLimitSoldering` (`canonical_clStageEquiv_bond`) |
| `algebraic direct limit` | Explicit Mathlib `DirectedSystem` / `_root_.DirectLimit` (or quotient `ClInf A`) with canonical injections (`DirectLimit.of`, `ofStage`, `toClInf`) and compatibility laws | `SplitCliffordDirectLimit` (`SplitCliffordInfinity`), `SplitCliffordHeadTailTower` (`SplitCliffordHeadTailInfinity`), `Cl11TensorTowerLimit` (`Limit`), `Cl11GradedDifferential` (`splitCliffordInfinityEquivLimit`), `SplitCliffordTowerUnification` (`DoubleCylinderColimit ℝ`), `NoncommutativeCliffordColimitMassGapSynthesis` (`ClInf`) |
| `discrete topological` | Maps proved continuous on explicit `DiscreteTopology` carriers (NOT Banach/C*-norm topology) | `Topology/SplitCliffordHeisenbergTopological.lean` |
| `analytic or topological completion` | Explicit `UniformSpace.Completion (ClInfOp A)` Banach `*`-algebra completion on Lane 3 (`ClInfOpCompletion A`), NOT on `SplitCliffordInfinity` | `Algebra/NoncommutativeColimitCStarCompletionAndOperatorSemigroup.lean`, `Algebra/NoncommutativeColimitBanachStarSemigroup.lean` |
| `open debt (BUCKET 3)` | Claims beyond current owner proofs (tautological scaffolds, deferred M3 integrations, `src/` mirror sync) | `Topology/CliffordMobiusDeRhamMonodromy.lean`, M3 tasks |

---

## 2. Formal Intent Envelopes (`ALCHEMICAL_QMS_SOP.md` §3.6)

### 2.1 `r3-f31-cl11-graded-towers-and-bases` (`F3.1`, M2.2)

```json
{
  "concept_id": "r3-f31-cl11-graded-towers-and-bases",
  "source_text": "Reconcile the three Cl(1,1) = M_2(R) basis conventions and bridge Cl(1,1)-tensored Z/2-graded towers (Clsplit n, SplitCliffordInfinity) with the recursive matrix tower (ClTower A n, ClInf A) and unital vs non-unital embeddings.",
  "intake_classification": "theorem-bearing",
  "classification": "graded Morita equivalence, 3-basis dictionary, and algebraic DirectLimit tower unification",
  "mathematical_domain": ["Cl(1,1)", "Z/2-graded Morita", "ClTower", "DirectLimit"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.Clifford.Cl11Matrix",
    "InfoGeometry.Clifford.Cl11GradedMorita",
    "InfoGeometry.Clifford.Cl11GradedTensorMorita",
    "InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis",
    "InfoGeometry.Canonical.Cl11MatrixCliffordBridge",
    "InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis",
    "InfoGeometry.Canonical.SplitCliffordDirectLimit",
    "InfoGeometry.Canonical.SplitCliffordHeadTailTower",
    "InfoGeometry.Canonical.SplitCliffordTowerUnification",
    "InfoGeometry.Topology.SplitCliffordHeisenbergTopological",
    "InfoGeometry.Clifford.CliffordTower",
    "InfoGeometry.Clifford.BottPeriodicity"
  ],
  "non_theorem_claims": [
    "Full real 8-fold Bott periodicity M_16(R) (Clifford.BottPeriodicity establishes only the split (n,n) -> (n+1,n+1) step clsplit_succ_equiv)",
    "Analytic C*-norm or UHF Banach completion on SplitCliffordInfinity (analytic completion lives on Lane 3 ClInfOpCompletion A)"
  ],
  "formal_objects": [
    "cl11EquivMat",
    "cl11StandardEquiv",
    "cl11MatrixAlgEquiv",
    "walshConjugation",
    "j1Conjugation",
    "tensorMatrixEquiv",
    "involutionGrading",
    "pPlus",
    "ClTower",
    "instAlgebraClTower",
    "bottEmbed",
    "diagEmbed",
    "cornerProj",
    "ClInf",
    "cantorProj",
    "SplitCliffordInfinity",
    "clSplitGradedTensorEquivClTower",
    "splitCliffordCornerStep"
  ],
  "acceptance_theorems": [
    "threeBasis_generator_table",
    "cl11StandardEquiv_involute",
    "tensorMatrixEquiv_pPlus_tmul",
    "bottEmbed_eq_cornerProj_mul_diagEmbed",
    "splitCliffordInfinity_stage_injective",
    "splitCliffordHeadTailInfinity_algEquiv",
    "clSplitGradedTensorEquivClTower_parity",
    "clSplitGradedTensorEquivClTower_splitCliffordStep",
    "clSplitGradedTensorEquivClTower_bottEmbed",
    "clSplitEquivClTowerReal"
  ]
}
```

### 2.2 `r3-f32-cl11-atom-symmetry` (`F3.2`, M2.2)

```json
{
  "concept_id": "r3-f32-cl11-atom-symmetry",
  "source_text": "Package the Cl(1,1) Klein four-group V_4 atom symmetry and head/diagonal reflections into SymmetryAction structures across Cl(1,1), evenOdd q11 g_tensor A, Clsplit n, SplitCliffordInfinity, and DoubleCylinderColimit R.",
  "intake_classification": "theorem-bearing",
  "classification": "equivariant V_4 atom symmetry on graded towers and algebraic direct limits",
  "mathematical_domain": ["Klein four-group V4", "SymmetryAction", "graded tensor product", "DirectLimit"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation",
    "InfoGeometry.Clifford.Cl11GradedTensorMorita",
    "InfoGeometry.Canonical.SplitCliffordTowerUnification",
    "InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants",
    "InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit"
  ],
  "non_theorem_claims": [
    "Standalone packaged theorem Function.Injective cl11V4SymmetryAction.act (faithful action proved elementwise / via invariants; named injectivity theorem deferred to M3)",
    "Standalone SymmetryAction V4 (Clsplit n) wrapper around diagV4ClsplitAuto (action propagated directly to diagV4InfinitySymmetryAction)"
  ],
  "formal_objects": [
    "localCl11Map",
    "cl11V4Auto",
    "walshV4Swap",
    "mat2V4SymmetryAction",
    "cl11V4SymmetryAction",
    "headLiftAlgEquiv",
    "headLiftSymmetryAction",
    "tensorHeadV4SymmetryAction",
    "headV4InfinitySymmetryAction",
    "diagV4ClsplitAuto",
    "diagV4InfinitySymmetryAction",
    "gSwapToV4",
    "doubleCylinderColimitV4SymmetryAction",
    "erlangenDoubleCylinderSymmetryAction"
  ],
  "acceptance_theorems": [
    "cl11EquivMat_v4Auto",
    "cl11StandardEquiv_v4Auto",
    "cl11V4_involute_comm",
    "cl11V4_invariant_iff_scalar",
    "tensorMatrixEquiv_headLift_involute",
    "tensorMatrixEquiv_headLift_splitReflection",
    "tensorMatrixEquiv_splitReflection_tmul_parity",
    "diagV4Infinity_T_eq_involute",
    "doubleCylinderColimitV4_restrict_gSwap",
    "localCl11AlgebraHom_v4_equivariant"
  ]
}
```

### 2.3 `r3-f33-graded-tensor-chains-and-differentials` (`F3.3`, M2.2)

```json
{
  "concept_id": "r3-f33-graded-tensor-chains-and-differentials",
  "source_text": "Reconcile homogeneous and single-site graded tensor chains with Jordan-Wigner differentials and homotopies on SplitCliffordInfinity and nativeChain, record the BondCoherence obstruction for naive recursive spinors, and connect exact and rank-minimal Clifford tensor trains.",
  "intake_classification": "theorem-bearing",
  "classification": "graded tensor chains, JW differential/homotopy transport, and matrix limit soldering",
  "mathematical_domain": ["CAR algebra", "Jordan-Wigner isomorphism", "graded differentials", "tensor trains"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.Clifford.Cl11HomogeneousChains",
    "InfoGeometry.Clifford.Cl11GradedDifferential",
    "InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering",
    "InfoGeometry.Clifford.Cl11TensorTowerLimit",
    "InfoGeometry.Clifford.Cl11TensorTrainSynthesis"
  ],
  "non_theorem_claims": [
    "Untwisted BondCoherence for naive spinorRepresentation (disproved by gradedTensorSuccessor_not_algHom; requires parity-twisted bond twistedStageEmbed or JW bit-word soldering canonicalCliffordUHFColimitEquiv)",
    "Analytic C*-norm completion of SplitCliffordInfinity under splitJWDifferential"
  ],
  "formal_objects": [
    "nativeChain",
    "ordinaryChain",
    "singleSiteChain",
    "prefixParity",
    "jwDifferential",
    "jwHomotopy",
    "jwSplitStageEquiv",
    "splitCliffordInfinityEquivLimit",
    "splitJWDifferential",
    "splitJWHomotopy",
    "nativeChainDifferential",
    "nativeChainHomotopy",
    "gradedTensorSuccessor",
    "twistedStageEmbed",
    "trainSynthesis",
    "trainMatrix"
  ],
  "acceptance_theorems": [
    "nativeChain_matrix_suffixParity",
    "unrollCoefficients_pure_chain_iff",
    "singleSiteChain_null_car",
    "gradedTensorSuccessor_not_algHom",
    "twisted_stageMap_generator_bond_native",
    "splitCliffordInfinityEquivLimit_involute",
    "splitJWDifferential_sq",
    "splitJWDifferential_range_eq_ker",
    "splitJWDifferential_leibniz",
    "nativeChainDifferential_nativeChain",
    "ofSplitStage_nativeChainDifferential",
    "exists_exact_clifford_train",
    "exists_minimal_clifford_train"
  ]
}
```

### 2.4 `r3-f34-coordinateless-clifford-invariance` (`F3.4`, M2.1)

```json
{
  "concept_id": "r3-f34-coordinateless-clifford-invariance",
  "source_text": "Characterize Clifford algebra symmetry-invariant geometry as a basis-free, coordinate-less representation of CliffordAlgebra Q properties under IsometryEquiv, O(Q), SO(Q), and V_4, while aligning ErlangenCoordinateless to its concrete M_2(C) Pauli spin-frame scope.",
  "intake_classification": "theorem-bearing",
  "classification": "coordinate-less CliffordAlgebra Q isometry invariance and O(Q)/SO(Q) invariant subalgebras",
  "mathematical_domain": ["CliffordAlgebra Q", "ExteriorAlgebra", "QuadraticForm.IsometryEquiv", "Erlangen 1872"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.Clifford.GradedGraceContraction",
    "InfoGeometry.Clifford.CoordinateLessCliffordInvariance",
    "InfoGeometry.Algebraic.CliffordSymmetryLift",
    "InfoGeometry.ErlangenCoordinateless",
    "InfoGeometry.Clifford.SplitClifford55ExteriorFiniteGraded"
  ],
  "non_theorem_claims": [
    "Analytic infinite-dimensional Hodge/Krein spectral theory beyond finite-dimensional real/field spaces",
    "Claiming ErlangenCoordinateless.lean M_2(C) identities formulate abstract O(Q) invariance on general CliffordAlgebra Q"
  ],
  "formal_objects": [
    "cliffordGradeProj",
    "cliffordGradeSubmodule",
    "cliffordKreinPairing",
    "kreinFlip31",
    "graceOperator",
    "cliffordSymmetryAction",
    "cliffordOperatorSymmetryAction",
    "detHom",
    "specialIsometrySubgroup",
    "v4ToQ11IsometryHom",
    "SplitQuadraticSymmetry",
    "splitCliffordLiftHom",
    "splitCliffordSymmetryAction"
  ],
  "acceptance_theorems": [
    "involute_equivOfIsometry",
    "reverse_equivOfIsometry",
    "evenOdd_map_equivOfIsometry",
    "cliffordGradeProj_equivOfIsometry",
    "hTrace_cl_equivOfIsometry",
    "cliffordKreinPairing_equivOfIsometry",
    "graceOperator_equivOfIsometry",
    "equivOfIsometry_top_grade_eq_det_smul",
    "isInvariant_cliffordSymmetryAction_iff_mem_range",
    "isInvariant_specialIsometry_iff",
    "cl11EquivMat_v4_equivOfIsometry",
    "splitClifford_invariant_iff_scalar",
    "erlangen_coordinateless_capstone"
  ]
}
```

### 2.5 `r3-f35-r3-r1-forms-and-rotor-spin-coupling` (`F3.5`, M2.3)

```json
{
  "concept_id": "r3-f35-r3-r1-forms-and-rotor-spin-coupling",
  "source_text": "Couple ZornDifferentialFormsCliffordBridge (FormHodgeCliffordData) to cliffordGradeProj/equivExterior and R1 DerivationExteriorCalculus, and lift Cartan-Hestenes rotor Darboux spin-connection Maurer-Cartan identities into abstract CliffordAlgebra Q and Spin(Q) ->* O(Q).",
  "intake_classification": "theorem-bearing",
  "classification": "R3 <-> R1 differential form pullback, Darboux spin-connection Maurer-Cartan, and Spin(Q) coupling",
  "mathematical_domain": ["DerivationExteriorCalculus", "MaurerCartanTower", "CliffordAlgebra.spinGroup"],
  "target_status": "theorem-backed",
  "risk_level": "R4",
  "allowed_imports": [
    "InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus",
    "InfoGeometry.OperatorAlgebra.MaurerCartanTower",
    "InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge",
    "InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis"
  ],
  "non_theorem_claims": [
    "Smooth manifold Fréchet atlas for general rotor fields U -> Spin(Q) beyond 1D Mat2 curves and algebraic derivation lanes (BUCKET 3)",
    "Zero-curvature equation ceCurvature K (thetaR K u) = 0 (false in general; thetaR satisfies d(thetaR) - thetaR ^ thetaR = 0 while thetaL u^-1 satisfies ceCurvature = 0)",
    "Topological de Rham / Bott / Buscher monodromy closure in CliffordMobiusDeRhamMonodromy.lean (BUCKET 3 tautological scaffold)"
  ],
  "formal_objects": [
    "FormHodgeCliffordData",
    "InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge.chevalleyAction",
    "cliffordMorphismGrade",
    "cliffordMorphismPullbackForm",
    "clRotorUnit",
    "clRotorFrameVector",
    "clRotorDarbouxConnection",
    "reverseCommutingLane",
    "spinGroupToIsometryHom",
    "cl11HyperbolicRotor"
  ],
  "acceptance_theorems": [
    "chevalleyAction_injective",
    "chevalleyAction_noncomm_witness",
    "cliffordMorphism_eq_sum_cliffordMorphismGrade",
    "cliffordHodgeDirac_equivOfIsometry",
    "cliffordMorphismPullbackForm_ceCurvature",
    "cliffordMorphismPullbackForm_ceCurvature_eq_zero",
    "clRotor_darboux_spin_connection_identity",
    "mem_cliffordGradeSubmodule_two_of_even_reverse_neg_finrank_le_three",
    "clRotorDarboux_maurerCartan",
    "clRotorDarboux_derivation_maurerCartan",
    "reverseCommutingLane_thetaR_reverse_eq_neg",
    "equivOfIsometry_spinGroupToIsometryHom",
    "cl11HyperbolicRotor_darboux",
    "cl11HyperbolicRotor_mem_spinGroup"
  ]
}
```

---

## 3. `F3.1` (`M2.2`): `Cl(1,1)`-Tensored Graded Towers, Three-Basis Reconciliation, and Lane 1 ↔ Lane 3 Unification

The base split Clifford algebra `Cl(1,1) = CliffordAlgebra q11` over `Vec11 := ℝ × ℝ` with `q11 (x, y) = x^2 - y^2` (`lean/InfoGeometry/Clifford/Cl11Matrix.lean:34, 38`) is algebra-isomorphic to `Mat2 := Matrix (Fin 2) (Fin 2) ℝ`. M2.2 reconciles all three historical `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)` basis conventions alongside the `SplitQuaternion` homomorphism `cl11MatrixRep` (`lean/InfoGeometry/Canonical/Cl11MatrixCliffordBridge.lean:63`) and unifies `Cl(1,1)`-tensored `ℤ/2`-graded towers across Lane 1 (`Clsplit n` / `SplitCliffordInfinity`) and Lane 3 (`ClTower A n` / `ClInf A`).

### 3.1 Three-Basis `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)` Dictionary

| Realization | `ι(1,0)` image | `ι(0,1)` image | `J₁ = ι(1,0)ι(0,1)` image | Parity `involute` in `Mat2` | Source Owner |
|---|---|---|---|---|---|
| `cl11EquivMat` | `Eplus` (`σ₃`) | `Eminus` (`iσ₂`) | `J1` (`σ₁`) | `J1`-conjugation (non-diagonal) | `Clifford/Cl11Matrix.lean:200` |
| `cl11StandardEquiv` (`cl11EquivMat.trans walshConjugation`) | `J1` (`σ₁`) | `-Eminus` (`-iσ₂`) | `Eplus` (`σ₃`) | Diagonal (`Eplus`-conjugation: even = diagonal, odd = off-diagonal) | `Clifford/Cl11GradedMorita.lean:73`, `Canonical/SplitCliffordTowerUnification.lean:143` |
| `cl11MatrixAlgEquiv` (`(cliffordQ11FormEquivCl11MatrixQ11.trans cl11StandardEquiv).trans j1Conjugation`) | `J1` (`σ₁`) | `Eminus` (`iσ₂`) | `-Eplus` (`-σ₃`) | `Eplus`-conjugation | `Synthesis/MathlibCliffordUniversalLiftSynthesis.lean:374`, `Canonical/SplitCliffordTowerUnification.lean:148, 205, 212` |

Verified declarations:
- **Carrier identification & noncommutativity**: `q11_eq_splitQ11` (`Cl11Matrix.lean:47`), `cliffordAlgebra_q11_eq_splitQ11` (`L55`), `q11ToSplitIsometry` (`L61`), `q11ToSplitClifford` (`L69`), and `J1_mul_Eminus_ne : J1 * Eminus ≠ Eminus * J1` (`L88`).
- **Explicit conjugation intertwiners**:
  - `walshConjugation : Mat2 ≃ₐ[ℝ] Mat2` (`Cl11GradedMorita.lean:42`), swapping `Eplus ↔ J1` and negating `Eminus` (`L57, L62, L67`);
  - `j1Conjugation : Mat2 ≃ₐ[ℝ] Mat2` (`SplitCliffordTowerUnification.lean:119`), fixing `J1` and negating `Eplus, Eminus`;
  - `cl11StandardEquiv_eq_walsh_trans_cl11EquivMat` (`L143`), `cl11MatrixAlgEquiv_eq_j1Conj_trans_cl11StandardEquiv` (`L148`), `cl11MatrixAlgEquiv_eq_walsh_j1_cl11EquivMat` (`L205`), and `threeBasis_generator_table` (`L212`).

### 3.2 `ℤ/2`-Graded Morita Equivalence & `evenOdd q11 ᵍ⊗[ℝ] 𝒜`

1. **Base `Cl(1,1)` Graded Morita (`lean/InfoGeometry/Clifford/Cl11GradedMorita.lean`, `268` lines)**:
   - `cl11StandardEquiv_involute` (`L119`) and `involute_eq_J1_cl_conj` (`L142`) prove that `CliffordAlgebra.involute` equals inner conjugation by `J1_cl` in `Cl(1,1)` and by `Eplus = diag(1, -1)` under `cl11StandardEquiv`.
   - `cl11StandardEquiv_grade` (`L148`), `cl11StandardEquiv_even_offDiagonal` (`L159`: proves off-diagonal matrix entries vanish for even elements, i.e., even = diagonal), and `cl11StandardEquiv_odd_diagonal` (`L172`: proves diagonal entries vanish for odd elements, i.e., odd = off-diagonal).
   - `cl11MoritaEquivalence` (`L186`), `cl11InnerGradedEquivalence` (`L192`), `cl11Module_grading_action` (`L196`), `cl11GradedEquivalence` (`L204`), and `freedPositiveLineRepresentation` (`L239`).
2. **Graded Tensor Morita (`lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean`, `1,029` lines)**:
   - For arbitrary noncommutative `[Ring A] [Algebra ℝ A]` equipped with `[GradedAlgebra 𝒜]` and involutive parity automorphism `θ : A ≃ₐ[ℝ] A`, `tensorMatrixEquiv` (`L233`) constructs the `ℤ/2`-graded tensor product isomorphism `evenOdd q11 ᵍ⊗[ℝ] 𝒜 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A` (with `tensor_matrix_units_noncomm` `L251`).
   - Bridges ungraded and involution-graded carriers via `trivialGrading` (`L354`), `instGradedAlgebraTrivialGrading` (`L357`), `tensorMatrixEquivUngraded` (`L399`), `ungradedTensorEquivMatrix` (`L458`), `involutionGrading` (`L472`), `instGradedAlgebraInvolutionGrading` (`L530`), and `matrixAlgGrade` (`L583`).
   - Corner idempotent `pPlus` (`L599`) satisfies `tensorMatrixEquiv_pPlus_tmul` (`L630`), embedding `A` into the `(0,0)` corner of `Matrix (Fin 2) (Fin 2) A`.

### 3.3 Five-Lane Tower Reconciliation & Unital vs. Non-Unital Boundary

| Lane | Carrier / Limit Type | Primary Owner(s) | Key Verified Objects & Theorems | Scope Tag |
|---|---|---|---|---|
| **Lane 1 (`Clsplit n` Direct Limit)** | `_root_.DirectLimit SplitClNNAlg splitCliffordMap` (`SplitCliffordInfinity`) | `Canonical/SplitCliffordDirectLimit.lean` (`385` lines) | `splitCliffordStep` (`L38`), `splitCliffordStep_tensorFactor` (`L49`), `splitCliffordMap` (`L119`), `splitCliffordMap_injective` (`L170`), `splitCliffordDirectedSystem` (`L183`), `SplitCliffordInfinity` (`L195`), `splitCliffordInfinity_stage_injective` (`L201`), `splitCliffordInfinity_cl55_window_absorbs_finite_tail` (`L324`), `splitCliffordInfinity_has_representative_beyond_cl55_window` (`L339`) | `algebraic direct limit` |
| **Lane 2 (Head-Tail Factorization)** | `SplitCliffordHeadTailInfinity k` (`≃+*`, `≃ₐ[ℝ]` `SplitCliffordInfinity`) | `Canonical/SplitCliffordHeadTailTower.lean` (`940` lines) | `splitCliffordHeadTailStep` (`L53`), `splitCliffordHeadTailStep_compatible` (`L147`), `splitCliffordHeadTailDirectedSystem` (`L199`), `SplitCliffordHeadTailInfinity` (`L339`), `splitCliffordHeadTailInfinity_ringEquiv` (`L761`), `splitCliffordHeadTailInfinity_algEquiv` (`L797`), `splitCliffordHeadTailInfinity_ringEquiv_grade_involution` (`L914`) | `algebraic direct limit` |
| **Lane 3 (`ClTower A n` & `ClInf A`)** | Recursive `ClTower A n` (`M₂(ClTower A n)`) & quotient `ClInf A` | `Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean` (`583` lines) | `ClTower` (`L67`), `instRingClTower` (`L71`), `@[reducible] def instAlgebraClTower` (`L77`), `chiralityOp` (`L134`), `superTrace` (`L138`), `bottEmbed` (`L148`), `diagEmbed` (`L152`), `cornerProj` (`L173`), `bottEmbed_eq_cornerProj_mul_diagEmbed` (`L180`), `diagEmbedAlgHom` (`L188`), `bottEmbedNonUnitalAlgHom` (`L199`), `ClInf` (`L324`), `cantorProj` (`L348`) | `finite stage` + `algebraic direct limit` |
| **Lane 1 ↔ Lane 3 Unification** | Iterated `evenOdd (Qsplit n) ᵍ⊗[ℝ] involutionGrading θ hθ ≃ₐ[ℝ] ClTower A n` & `Clsplit n ≃ₐ[ℝ] ClTower ℝ n` | `Canonical/SplitCliffordTowerUnification.lean` (`3,501` lines, §§2–3) | `clTowerParity` (`L255`), `clTowerGrading` (`L268`), `instGradedAlgebraClTower` (`L272`), `gradedSplitZeroTensorEquiv` (`L371`), `gradedTensorMapAlgHom` (`L433`), `clSplitGradedTensorEquivClTower` (`L1401`), `_parity` (`L1406`), `gradedTrivialTensorEquiv` (`L1459`), `clTowerEquivCliffordTensor` (`L1570`), `clTowerEquivMatrix` (`L1577`), `clSplitEquivClTowerReal` (`L1582`), `splitCliffordCornerStep` (`L1700`, `→ₙₐ[ℝ]`), `clSplitGradedTensorEquivClTower_splitCliffordStep` (`L1784`), `_diagEmbed_even` (`L1833`), `_bottEmbed` (`L1845`), `splitChiralityElement` (`L1918`), `splitCantorProj` (`L2022`) | `staged theorem transported by explicit successor maps` |
| **Lane 5 (Discrete Topological, Mersenne, Split Bott)** | `DiscreteTopology` Heisenberg/Sugawara & `2^n - 1` | `Topology/SplitCliffordHeisenbergTopological.lean` (`138` lines), `Clifford/CliffordTower.lean` (`144` lines), `Clifford/BottPeriodicity.lean` (`112` lines) | `topologicalSplitCliffordToCurrentHeisenbergRep` (`L73`), `continuous_...` (`L87`), `topologicalSplitCliffordToCurrentSugawaraMorphism` (`L105`), `mersenne` (`L44`), `mersenne_growth` (`L104`), `parafermion_centralizer_dim` (`L117`), `clsplit_succ_equiv` (`Clifford/Tower.lean:65`) | `discrete topological` / `finite stage` |

Key structural boundaries established in M2.2:
1. **Diamond-free `instAlgebraClTower` scoping**: In `NoncommutativeCliffordColimitMassGapSynthesis.lean:77, 184–207`, `instAlgebraClTower` is a `@[reducible] def` activated exclusively via `attribute [local instance]` inside closed sections so zero global `SMul ℝ (ClTower A n)` diamond leaks into `NoncommutativeColimitNormedLindbladBridge`.
2. **Unital vs. Non-Unital Bond Reconciliation**: `tensorMatrixEquiv_one_tmul_eq_mat2_of_even` (`SplitCliffordTowerUnification.lean:1615`), `tensorMatrixEquiv_one_tmul_eq_twistedDiag` (`L1624`), `tensorMatrixEquiv_one_tmul_eq_diagEmbed` (`L1634`), and `tensorMatrixEquiv_diagEmbed_symm` (`L1646`) track the parity sign between `1 ᵍ⊗ₜ x` and `diagEmbed x`, whereas `tensorMatrixEquiv_pPlus_tmul_eq_bottEmbed` (`L1689`), `splitCliffordCornerStep` (`L1700`, non-unital `→ₙₐ[ℝ]`), and `clSplitGradedTensorEquivClTower_bottEmbed` (`L1845`) reconcile `bottEmbed` without conflating unital `SplitCliffordInfinity` and non-unital `ClInf A`.
3. **Analytic Completion Separation**: `SplitCliffordInfinity` is purely an algebraic `_root_.DirectLimit`; the Banach `*`-algebra completion `ClInfOpCompletion A := UniformSpace.Completion (ClInfOp A)` lives on Lane 3 (`NoncommutativeColimitCStarCompletionAndOperatorSemigroup.lean:266`). Similarly, `Clifford/BottPeriodicity.lean` packages only the split `(n,n) ↦ (n+1,n+1)` step `clsplit_succ_equiv`, not 8-fold real Bott periodicity.

---

## 4. `F3.2` (`M2.2`): `Cl(1,1)` Atom Symmetry Across `Cl(1,1)`, Graded Towers, and `DoubleCylinderColimit ℝ`

1. **Base `V₄` Atom Symmetry (`lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean`, `660` lines)**:
   - `adjointAlgHom` (`L135`), `localCl11RootMap` (`L293`), and `localCl11Map : V4 →* (Mat2 ≃ₐ[ℝ] Mat2)` (`L299`) realize the Klein four-group by inner conjugation of `Eplus, J1, Eminus`.
   - `centralInversion` (`L311`) and `clifford_equivOfIsometry_centralInversion` (`L336`, `= involuteEquiv`) link `V₄` to `CliffordAlgebra.equivOfIsometry`.
   - `cl11V4RootAuto` (`L387`) and `cl11V4Auto : V4 →* (CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11)` (`L394`) intertwine with `Mat2` under both bases via `cl11EquivMat_v4Auto` (`L414`) and `walshV4Swap` (`L462`) / `cl11StandardEquiv_v4Auto` (`L495`, swapping `P ↔ T`).
   - `mat2V4SymmetryAction` (`L553`) and `cl11V4SymmetryAction : SymmetryAction V4 (CliffordAlgebra q11)` (`L562`) satisfy `cl11V4_involute_comm` (`L572`), `mat2V4_invariant_iff_scalar` (`L600`), and `cl11V4_invariant_iff_scalar` (`L640`).
2. **Head Lift & Koszul Sign Intertwining (`lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean`)**:
   - `headLiftAlgHom` (`L712`), `headLiftAlgEquiv` (`L751`), `headLiftSymmetryAction` (`L799`), and `matrixScalarAdjoint` (`L828`) lift `Cl(1,1)` automorphisms onto `evenOdd q11 ᵍ⊗[ℝ] 𝒜`.
   - `tensorMatrixEquiv_headLift_involute` (`L908`), `tensorMatrixEquiv_headLift_splitReflection` (`L939`), `tensorMatrixEquiv_headLift_splitReflectionFirstCoordinate` (`L973`), and `tensorMatrixEquiv_splitReflection_tmul_parity` (`L1011`) prove exact Koszul-sign commutation with `tensorMatrixEquiv`.
3. **Tower-Level & Double-Cylinder Propagation (`SplitCliffordTowerUnification.lean` §4 & `ErlangenDoubleCylinderSymmetryInvariants.lean`)**:
   - Head `V₄` actions: `tensorHeadV4Action` (`L2091`), `tensorHeadV4SymmetryAction` (`L2119`), `tensorMatrixEquiv_headV4_equivariant` (`L2152`), `headV4ClsplitOneAuto` (`L2178`), `headV4HeadTailStageAuto` (`L2199`), and `headV4InfinitySymmetryAction` (`L2456`).
   - Diagonal `V₄` actions: `diagV4Isometry` (`L2512`), `diagV4ClsplitAuto` (`L2606`), `diagV4ClsplitAuto_bond` (`L2630`), `diagV4InfinityAuto` (`L2769`), `diagV4InfinitySymmetryAction` (`L2834`), and `diagV4Infinity_T_eq_involute` (`L2863`).
   - `DoubleCylinderColimit ℝ` compatibility (`OperatorAlgebra/CantorDoubleCylinderFractalColimit.lean:303` and `OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean:59, 131, 212, 227, 252, 282, 364`): `gSwapToV4` (`SplitCliffordTowerUnification.lean:2877`), `doubleCylinderStageEquivMat2` (`L2903`), `stageSwapEquiv_one_eq_localCl11Map_T` (`L2908`), `matTowerLimitV4SymmetryAction` (`L3082`), `realCantorLimitV4SymmetryAction` (`L3119`), `matTowerLimitEquivDoubleCylinderColimit` (`L3165`), `doubleCylinderColimitV4SymmetryAction` (`L3191`), `doubleCylinderColimitV4_restrict_gSwap` (`L3285`, restricting `V₄` to `erlangenDoubleCylinderSymmetryAction ℝ`), `localCl11AlgebraHom_v4_equivariant` (`L3310`), and `mat2_noncomm_witness` (`L3493`).

---

## 5. `F3.3` (`M2.2`): Graded Tensor Chains, JW Differentials, Soldering Boundary, and Tensor Trains

1. **Homogeneous Chains, `prefixParity` / `suffixParity`, and CAR Generators (`lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean`, `935` lines)**:
   - `nativeChain` (`L38`) vs `ordinaryChain` (`L147`): `nativeChain_homogeneous` (`L110`), `nativeChain_matrix_suffixParity` (`L192`), `unrollNative_ordinaryChain_suffixParity` (`L243`), `coefficientChain_matrix_suffixParity` (`L293`), and `unrollCoefficients_pure_chain_iff` (`L384`: exact rank-1 pure-chain criterion for unrolled tensor chains).
   - Null CAR creation/annihilation chains: `nullPlus` (`L395`), `nullMinus` (`L399`), `singleSiteChain` (`L444`), `singleSiteChain_homogeneous` (`L488`), `leftMatrixEquiv_singleSiteChain_nullPlus` (`L592`), `prefixParity` (`L618`), `singleSiteChain_mul_nativeChain_homogeneous` (`L761`), `nativeChain_mul_singleSiteChain_homogeneous` (`L810`), `totalParity_xor_suffixParity` (`L861`), and `singleSiteChain_null_car` (`L911`).
2. **Matrix-Limit Soldering & `BondCoherence` Obstruction (`lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean`, `972` lines; `Clifford/Cl11TensorTowerLimit.lean`, `252` lines)**:
   - `stageMap` (`L77`) transports the recursive `spinorRepresentation` to `MatrixStage n`; its linear successor `gradedTensorSuccessor` (`L160`) appends `gradingAtom ≠ 1`, so **`gradedTensorSuccessor_not_algHom` (`L779`) proves `BondCoherence` (`L807`) is FALSE** for naive `spinorRepresentation` against the untwisted bond `stageEmbed` (`matrixLimitMap` at `L813` is explicitly conditional on `BondCoherence`).
   - Two valid routes resolve this obstruction:
     - **Route B (Parity-Twisted Bond)**: `twistedStageEmbed` (`L520`) acts as `A_even ⊗ I₂ + A_odd ⊗ γ₁₂`, satisfying `twisted_stageMap_generator_bond_native` (`L581`);
     - **Route A (Unconditional JW Bit-Word Soldering)**: `canonicalCliffordUHFColimitEquiv` (`L919`) unconditionally solders the matrix tower limit (`Cl11TensorTowerLimit.Limit`, `L20`) to the UHF colimit.
3. **Jordan–Wigner Differentials & Homotopies on `SplitCliffordInfinity` and `nativeChain` (`lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean`, `1,338` lines)**:
   - Finite-stage JW soldering: `jwDifferential` (`L46`), `jwHomotopy` (`L77`), `canonicalCliffordUHFColimitEquiv_smul` (`L144`), `canonicalCliffordUHFColimitLinearEquiv` (`L163`), `jwSplitStageHom` (`L379`), `nativeJWCreation` (`L450`), `nativeJWAnnihilation` (`L454`), `jwSplitStageHom_bond` (`L528`), `jwSplitStageHom_surjective` (`L571`), `jwSplitStageEquiv` (`L694`), and direct-limit isomorphism `splitCliffordInfinityEquivLimit : SplitCliffordInfinity ≃ₐ[ℝ] Cl11TensorTowerLimit.Limit` (`L799`) intertwining `splitCliffordInfinityInvoluteEquiv` (`L824`, `L933`).
   - Direct-limit differential & homotopy: `splitJWDifferential` (`L957`), `splitJWHomotopy` (`L961`), `splitJWDifferential_sq` (`L988`), `splitJWDifferential_annihilation` (`L1004`), `splitJWDifferential_ne_zero` (`L1010`), `splitJWDifferential_homotopy` (`L1018`), `splitJWDifferential_range_eq_ker` (`L1038`), `splitJWDifferential_leibniz` (`L1053`), and `mat2_noncomm_witness` (`L1063`).
   - Finite-stage `nativeChain` differential & `Fin.rev` site-order duality: `nativeChainDifferential` (`L1091`), `nativeChainHomotopy` (`L1096`), `_sq` (`L1107`), `_homotopy` (`L1136`), `_range_eq_ker` (`L1151`), `_leibniz` (`L1167`), `nativeChainDifferential_nativeChain` (`L1225`, carrying `prefixParity`), `leftMatrixEquiv_nativeChainDifferential_homogeneous` (`L1251`), `singleSiteChain_iota_eq_splitCoord_rev` (`L1278`), `ofSplitStage_nativeChainDifferential` (`L1319`), and `ofSplitStage_nativeChainHomotopy` (`L1329`).
4. **Exact & Minimal-Bond Clifford Tensor Trains (`lean/InfoGeometry/Clifford/Cl11TensorTrainSynthesis.lean`, `111` lines)**:
   - `trainSynthesis` (`L39`), `trainMatrix` (`L43`), `trainMatrix_eq_iff` (`L52`), `exists_exact_clifford_train` (`L70`, over arbitrary `[Ring B] [Algebra ℝ B]`), `exists_minimal_clifford_train` (`L85`, attaining exact cut ranks over `ℝ`), and `clifford_cutRank_le` (`L105`: `≤ 4 ^ min k m`).

---

## 6. `F3.4` (`M2.1`): Coordinate-Less Clifford Invariance & Klein 1872 Grounding

### 6.1 Historical Grounding (Felix Klein 1872 *Erlanger Programm*)

The coordinate-less invariance architecture of `F3.4` implements Felix Klein's 1872 *Vergleichende Betrachtungen über neuere geometrische Forschungen* (*Erlanger Programm*; digitized primary source `ABN7632.0001.001`; English translation by M. W. Haskell, *Bull. New York Math. Soc.* **2** (1892–1893), 215–249, `arXiv:0807.3161v1`), verified directly in `CoordinateLessCliffordInvariance.lean:46–70, 229–236, 382–386, 1005–1009`, `ErlangenCoordinateless.lean:27–37, 163–168`, and `SplitCliffordTowerUnification.lean:33–42`:

- **Concluding Remarks & Footnote 37 (*coordinate-system-independent invariant analytic formalisms*)**: Klein explicitly contrasts concrete coordinate-frame expressions with coordinate-system-independent invariant analytic formalisms. In R3, the concrete `M₂(ℂ)` Pauli spin-frame (`ErlangenCoordinateless.lean`) and the three `M₂(ℝ)` bases (`cl11EquivMat`, `cl11StandardEquiv`, `cl11MatrixAlgEquiv`) are coordinate realizations, whereas the intrinsic invariant theory lives on arbitrary `(M, Q)` via `Q.IsometryEquiv Q →* (CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q)` (`CliffordAlgebra.equivOfIsometry`) and `spinGroupToIsometryHom : spinGroup Q →* Q.IsometryEquiv Q`.
- **§4 (*Abbildung* / Transfer by Representation)**: Equivariant maps conjugate transformation groups and transport invariant theories: `equivExterior_equivOfIsometry`, `cl11EquivMat_v4_equivOfIsometry`, `walshConjugation`, `j1Conjugation`, `clSplitGradedTensorEquivClTower`, `clTowerEquivCliffordTensor`, `splitCliffordInfinityEquivLimit`, and `matTowerLimitEquivDoubleCylinderColimit`.
- **§5 & Footnotes 22–23 (*choice of space-element & faithful orbits*)**: Excluding elements stabilized by a nontrivial normal ("self-conjugate") subgroup is required for faithful group representation. The central reflection `{1, negIsometryEquiv Q} ≃ ℤ/2` is a nontrivial normal subgroup of `O(Q)` stabilizing `evenOdd Q 0` (`equivOfIsometry_neg_fixed_iff_mem_even`), yielding the exact faithfulness classification documented in `CoordinateLessCliffordInvariance.lean:229–236`:
  - On full `CliffordAlgebra Q`, `O(Q)` acts faithfully when `M` is nontrivial (for `dim M ≥ 1`).
  - On `evenOdd Q 0`: `O(Q)/{±id}` acts faithfully for `dim M ≥ 3`, `dim M = 0`, or `dim M = 1` with `Q ≠ 0`; for `dim M = 2`, `SO(Q)` stabilizes `evenOdd Q 0 = grade 0 ⊔ grade 2` so only `O(Q)/SO(Q)` acts faithfully; for `dim M = 1` with `Q = 0`, `evenOdd 0 0 = K` is completely fixed.

### 6.2 Universal `IsometryEquiv` Transport (`GradedGraceContraction.lean` & `SplitClifford55ExteriorFiniteGraded.lean`)

- `lean/InfoGeometry/Clifford/SplitClifford55ExteriorFiniteGraded.lean` (`83` lines): `exteriorAlgebraFiniteGradedEquiv` (`L57`), `exteriorAlgebraFiniteBasis` (`L66`), `gradedDirectSumFin_finrank` (`L71`).
- `lean/InfoGeometry/Clifford/GradedGraceContraction.lean` (`1,785` lines; Parts A–E + **Part F `section IsometryInvariance`, `L1330–1785`, 37 declarations**):
  - Core graded infrastructure: `exteriorGradeProj` (`L91`), `cliffordGradeProj` (`L180`, `[Invertible (2 : R)]`), `cliffordGradeProj_zero_eq_algebraMap_hTrace` (`L277`), `graceOperator` (`L537`), `graceInverseOperator` (`L541`), `cliffordKreinPairing` (`L1207`), `kreinFlip31` (`L1281`), `cliffordGradeSubmodule` (`L1678`), `mem_cliffordGradeSubmodule_iff` (`L1682`).
  - Part F `GeneralRing` (`[CommRing R]`): `Q_map_isometry` (`L1340`), `involute_equivOfIsometry` (`L1368`), `reverse_equivOfIsometry` (`L1384`), `star_equivOfIsometry` (`L1395`), `evenOdd_map_equivOfIsometry` (`L1421`), `equivOfIsometry_mem_evenOdd_iff` (`L1433`).
  - Part F `InvertibleTwo` (`[Invertible (2 : R)]`): `equivExterior_equivOfIsometry` (`L1642`), `cliffordGradeProj_equivOfIsometry` (`L1671`), `hTrace_cl_equivOfIsometry` (`L1706`), `cliffordKreinPairing_equivOfIsometry` (`L1711`).
  - Part F `RealGraceInvariance` (`R = ℝ`): `graceOperator_equivOfIsometry` (`L1761`) and `graceInverseOperator_equivOfIsometry` (`L1771`, using `LinearEquiv.finrank_eq`).

### 6.3 Coordinate-Less `O(Q)` / `SO(Q)` / `V₄` Subalgebras (`CoordinateLessCliffordInvariance.lean`, `1,197` lines)

Reuses `InfoGeometry.Clifford.quadraticIsometryEquivGroup` (`RealQuadraticReflection.lean`) with zero competing `Group` instances:
- **Actions & Equivariant Readouts**: `cliffordSymmetryAction` (`L92`), `cliffordOperatorSymmetryAction` (`L116`, `toFun g := equivOfIsometry g⁻¹`), `toSymmetryAction_cliffordOperatorSymmetryAction` (`L137`), `hTraceInvariantReadout` (`L184`), `cliffordKreinInvariantPairing` (`L194`), `cliffordSymmetryAction_equivariant_gradeProj` (`L205`), `graceOperator_equivariantLinearMap` (`L217`).
- **Parity & Negation Isometry**: `negIsometryEquiv` (`L243`), `equivOfIsometry_negIsometryEquiv` (`L259`, `= CliffordAlgebra.involuteEquiv`), `involute_eq_self_iff_mem_even` (`L307`), `equivOfIsometry_neg_fixed_iff_mem_even` (`L339`), `involute_eq_neg_self_iff_mem_odd` (`L345`).
- **Top-Grade Determinant & Exact `O(Q)`/`SO(Q)` Characterization**: `detHom` (`L395`), `specialIsometrySubgroup` (`L411`), `equivOfIsometry_top_grade_eq_det_smul` (`L516`), `equivOfIsometry_top_grade_fixed_of_mem_SO` (`L535`), `isInvariant_cliffordSymmetryAction_iff_mem_range` (`L890`: for any `[Field K] [Invertible (2 : K)] [Module.Finite K M]`, **no nondegeneracy hypothesis**, `(CliffordAlgebra Q)^{O(Q)} = range (algebraMap K _)`), `invariantSubring_cliffordSymmetryAction` (`L923`), `isInvariant_specialIsometry_iff` (`L933`: `(CliffordAlgebra Q)^{SO(Q)} = grade 0 ⊔ grade (finrank K M)`), `isInvariant_real_iff_hTrace_eq` (`L985`), and `isInvariant_real_iff_grace_fixed` (`L995`).
- **`Cl(1,1)` `V4Group` Invariance**: `v4ToQ11IsometryHom` (`L1025`), `cl11EquivMat_v4_equivOfIsometry` (`L1068`), `v4_invariant_cl11_iff_scalar` (`L1127`), `v4ToQ11IsometryHom_invariant_iff_scalar` (`L1175`), `cl11_noncommutative_witness` (`L1186`).

### 6.4 Split-Algebra Symmetry Lift & Concrete `ErlangenCoordinateless` Scope

- **`lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` (`259` lines)**: Defines `SplitQuadraticSymmetry` (`L39`) with `instGroup` (`L99`) transported via `splitQuadraticSymmetryMulEquiv` (`L126`), `splitCliffordLift` (`L62`), `splitCliffordLiftHom` (`L136`), `splitCliffordSymmetryAction` (`L154`), `splitCliffordOperatorSymmetryAction` (`L174`), `toSymmetryAction_splitCliffordOperatorSymmetryAction` (`L199`), `splitCliffordLift_ι_sq` (`L205`), `splitCliffordLift_involute` (`L210`), `splitCliffordLift_reverse` (`L215`), `splitCliffordLift_evenOdd_map` (`L220`), `splitCliffordLift_mem_evenOdd_iff` (`L226`), `splitCliffordLift_cliffordGradeProj` (`L232`), `splitCliffordLift_hTrace_cl` (`L238`), and `splitClifford_invariant_iff_scalar` (`L245`).
- **`lean/InfoGeometry/ErlangenCoordinateless.lean` (`190` lines)**: Explicitly scoped as `BUCKET 1` concrete `Matrix (Fin 2) (Fin 2) ℂ` Pauli spin-frame (`sigma`) identities (`jacobi_identity` `L81`, `bracket_antisymm` `L90`, `bianchi_is_jacobi` `L102`, `pauli_squares` `L126`, `pauli_s1_s2_not_commute` `L131`, `trace_of_commutator` `L148`, `erlangen_coordinateless_capstone` `L170`), explicitly redirecting to `InfoGeometry.Clifford.CoordinateLessCliffordInvariance` for genuine basis-free `O(Q)` invariance on `CliffordAlgebra Q`.

---

## 7. `F3.5` (`M2.3`): R3 ↔ R1 Coupling — Graded Forms, Hodge–Dirac, Cartan–Hestenes Rotor Spin Connections, and `Spin(Q)`

M2.3 couples the R3 graded Clifford/isometry layers (`ZornDifferentialFormsCliffordBridge.lean`, `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean`) directly to R1's `DerivationExteriorCalculus.lean` and `MaurerCartanTower.lean`.

### 7.1 `FormHodgeCliffordData`, `equivExterior` Transport, and Faithful `chevalleyAction` (`ZornDifferentialFormsCliffordBridge.lean`)

Preserves pre-existing `L24–150` (`FormHodgeCliffordData` at `L71` with generator field `D.generator : V →ₗ[R] C` at `L80`, `hodgeDirac` at `L83`, `cliffordMorphism` at `L117`) and adds non-vacuity witness `witnessFormHodgeCliffordData` (`L188`, with `differential := lmul (ι ![1, 0]) ≠ 0` and `hodgeStar := LinearMap.id`):

1. **Section A — Hodge Codifferential (`L153–204`)**: `hodgeCodifferential` (`L157`), `hodgeDirac_eq_add_codifferential` (`L166`), `hodgeCodifferential_sq` (`L171`), `hodgeDirac_comp_hodgeDirac` (`L179`).
2. **Section B1 — `equivExterior`-Transported Clifford Operators (`L219–309`)**: `cliffordDifferential` (`L223`), `cliffordHodgeStar` (`L229`), `cliffordCodifferential` (`L235`), `cliffordHodgeDirac` (`L241`), and identities `_sq` (`L270, L277, L284`), `_eq_add` (`L294`), `_comp_cliffordHodgeDirac` (`L302`).
3. **Section B2 — Faithful Noncommutative `chevalleyAction` (`L311–409`)**:
   - `InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge.chevalleyAction` (`L319–324`, disambiguated from `InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis.chevalleyAction` at `L177`) is defined directly by conjugating left multiplication `LinearMap.mul R (CliffordAlgebra D.Q) a` across Mathlib's `CliffordAlgebra.equivExterior D.Q`, without forcing `C` to commute.
   - Proved properties: `chevalleyAction_one_apply` (`L363`), `chevalleyAction_injective` (`L373`, via evaluation at `1 : ExteriorAlgebra R V`), `chevalleyAction_noncomm_witness` (`L381`), `chevalleyAction_ι_sq` (`L395`), `chevalleyAction_cliffordGradeProj_one` (`L402`).
4. **Section B3 & C — Grade Resolution & `equivOfIsometry` Equivariance (`L411–651`)**:
   - `cliffordMorphismGrade` (`L413`), `exteriorToTarget` (`L418`), `cliffordMorphismGrade_zero` (`L452`, `= algebraMap R C (hTrace_cl D.Q x)`), `cliffordMorphismGrade_one_ι` (`L459`, evaluating to `D.generator v` at `L460`), `cliffordDifferential_grade_raising` (`L493`), `hTrace_cl_cliffordDifferential_grade_eq_zero` (`L510`), and finite-dimensional real decomposition `cliffordMorphism_eq_sum_cliffordMorphismGrade` (`L526`, summing over `Finset.range (Module.finrank ℝ V_real + 1)` at `L529`).
   - Section C equivariance (`L545–651`): `chevalleyAction_equivOfIsometry` (`L554`), and (conditional on explicit intertwining hypotheses `hd`, `hs` since e.g. `witnessFormHodgeCliffordData` is not `O(2)`-equivariant) `cliffordDifferential_equivOfIsometry` (`L564`), `cliffordHodgeStar_equivOfIsometry_of_sign` (`L578`), `cliffordHodgeDirac_equivOfIsometry` (`L593`), `cliffordMorphism_equivOfIsometry` (`L618`), `cliffordMorphismGrade_equivOfIsometry` (`L631`), and `cliffordMorphismGrade_zero_equivOfIsometry` (`L644`).

### 7.2 R3 ↔ R1 Differential Forms & Curvature Pullback (`ZornDifferentialFormsCliffordBridge.lean` §D, `L655–1063`)

Given `K : LieActionLane R A` (or `K : DerivationLieLane R A`), `φ : K.L →ₗ[R] CliffordAlgebra Q` (or `K_C.L →ₗ[R] K.L`), and `FormHodgeCliffordData`:
- **Alternating/Exterior Cochain Bridge**: `cliffordAlternatingEval` (`L670`), `pullbackFormFamily` (`L719`), `cliffordAlternatingEval_cliffordGradeProj` (`L784`), `cliffordGradeProjForm` (`L806`), `cliffordHTraceForm` (`L820`).
- **Functoriality on `ActionOperatorForm` / `DerivationOperatorForm`**: `cliffordMorphismPullbackForm` (`L869`) satisfies `cliffordMorphismPullbackForm_actionExteriorDerivative` (`L927`), `cliffordMorphismPullbackForm_actionWedge` (`L961`), `cliffordMorphismPullbackForm_ceExteriorDerivative` (`L994`), `cliffordMorphismPullbackForm_ceWedge` (`L1010`), `cliffordMorphismPullbackForm_ceCurvature` (`L1025`), and `cliffordMorphismPullbackForm_ceCurvature_eq_zero` (`L1045`).

### 7.3 Abstract `CliffordAlgebra Q` Rotor, Darboux Spin Connection, and Maurer–Cartan Coupling (`CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean`)

Preserves Sections 1–3 (`L65–432`: `Matrix (Fin m) (Fin m) ℝ` / `M₂(ℝ)` rotor identities `cartan_hestenes_rotor_darboux_spin_connection_identity` `L226`, `einstein_cartan_sciama_kibble_contortion_spin_locking` `L320`, `maurer_cartan_spin_and_spin_connection_unification` `L395`) and lifts the theory to abstract `CliffordAlgebra Q` in Sections 4–5 (`L435–1532`):

1. **Sections 4A–4B (`L435–585`)**: `clRotorUnit` (`L443`: `R⁻¹ = reverse R`), `clRotorFrameVector` (`L463`: `R * γ * reverse R`), `clRotorConjugateAlgEquiv` (`L467`), `clRotorFrameVector_ι_sq` (`L503`), `clRotorDarbouxConnection R dR := dR * reverse R` (`L521`), `clRotor_darboux_spin_connection_identity` (`L530`: `d(R γ R̃) = [Ω, R γ R̃] + R(dγ)R̃`; constant-frame `L566`), and `clRotorDarbouxConnection_reverse_eq_neg` (`L577`).
2. **Section 4C (`L587–831`, `[Invertible (2 : R_coeff)]`)**: `changeForm_reverse` (`L666`), `equivExterior_reverse` (`L692`), `exteriorPower_two_reverse` (`L702`), `cliffordGradeProj_two_reverse` (`L722`), `cliffordGradeSubmodule_two_reverse` (`L736`), `hTrace_cl_reverse` (`L743`), `hTrace_cl_eq_zero_of_reverse_eq_neg` (`L760`), and `mem_cliffordGradeSubmodule_two_of_even_reverse_neg_finrank_le_three` (`L779`): over `[Module.Finite ℝ M_real]` with `Module.finrank ℝ M_real ≤ 3`, every even `x` with `reverse x = -x` lies in `cliffordGradeSubmodule Q_real 2`. *(Exact sharpness: `k = 4` has `reverse = (-1)^(4·3/2) = +1`, while in `dim ≥ 6` a 6-blade `blade6` is even with `reverse = (-1)^(6·5/2) = -1` and `cliffordGradeProj Q6 2 blade6 = 0`.)*
3. **Section 4D — Coupling to R1 `MaurerCartanTower` (`L833–1043`)**:
   - `clRotorDarbouxConnection_eq_actionThetaR` (`L840`), `clRotorDarbouxConnection_eq_thetaR` (`L852`: `Ω(D) = thetaR K u ![D] = -(thetaL K u⁻¹ ![D]) = -(pureGaugeForm ...)`), `clRotor_actionExteriorDerivative_frame` (`L876`, `_const` `L925`).
   - **Exact Maurer–Cartan Sign Consistency**:
     - `clRotorDarboux_maurerCartan` (`L941`): proves `actionExteriorDerivative K 1 (actionThetaR K u) - actionWedge K (actionThetaR K u) (actionThetaR K u) = 0` (`dΩ - Ω ∧ Ω = 0`, matching R1's right-logarithmic equation in `SPEC-R1-NCG-DIFFGEOM` §3.2).
     - `clRotorDarboux_derivation_maurerCartan` (`L952`): proves `ceExteriorDerivative K 1 (thetaR K u) = ceWedge K (thetaR K u) (thetaR K u) ∧ ceCurvature K (thetaL K u⁻¹) = 0`. *(Because `ceCurvature K Γ = dΓ + Γ ∧ Γ`, `ceCurvature K (thetaR K u) = 2 • ceWedge K (thetaR K u) (thetaR K u)` is generally nonzero; flatness `ceCurvature = 0` holds for `thetaL K u⁻¹ = -thetaR K u`.)*
   - `reverseCommutingDerivations` (`L965`), `reverseCommutingLane` (`L983`), `innerBivectorDerivation` (`L989`), `reverseCommutingLane_thetaR_reverse_eq_neg` (`L1009`).

### 7.4 `Spin(Q)` Double Cover & `Cl(1,1)` Hyperbolic Rotor Specialization (`L1045–1532`)

- **Section 4E (`L1045–1287`)**: `spinGroupIsometryEquiv` (`L1089`), `spinGroupToIsometryHom : spinGroup Q →* Q.IsometryEquiv Q` (`L1213`), `equivOfIsometry_spinGroupToIsometryHom` (`L1233`: conjugation `g * x * g⁻¹`), invariance corollaries (`spinGroup_conj_cliffordGradeProj` `L1249`, `_hTrace_cl` `L1257`, `_cliffordKreinPairing` `L1262`), and `splitSpinToQuadraticSymmetryHom` (`L1271`) / `splitCliffordLift_splitSpinToQuadraticSymmetryHom` (`L1277`) bridging `SplitSpinGroup n` (`lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean:51`) to `SplitQuadraticSymmetry n`.
- **Section 5 (`L1295–1532`)**:
  - `cl11HyperbolicRotor (θ : ℝ) := Real.cosh θ • (1 : CliffordAlgebra q11) + Real.sinh θ • J1_cl` (`L1304`) and `cl11HyperbolicRotorDeriv θ := Real.sinh θ • 1 + Real.cosh θ • J1_cl` (`L1308`).
  - `reverse_J1_cl` (`L1311`), `J1_cl_mem_cliffordGradeSubmodule_two` (`L1320`), `cl11HyperbolicRotor_mul_reverse` (`L1349`), and **`cl11HyperbolicRotor_darboux` (`L1395`: `clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ) = J1_cl`)**.
  - `cl11HyperbolicRotor_mem_spinGroup` (`L1434`: constructive factorization into timelike vectors `(0, -1)` and `(Real.sinh θ, Real.cosh θ)` matching Mathlib's `star_ι = -ι` unitary convention).
  - Matrix equivalences to Sections 1–3 (`hyperbolicRotor_hasDerivAt` at `L160` provides the analytic `HasDerivAt` on `Mat2`): `cl11EquivMat_cl11HyperbolicRotor` (`L1470`), `cl11EquivMat_cl11HyperbolicRotor_darboux` (`L1478`), `walshConjugation_cl11EquivMat_hyperbolicRotor` (`L1489`), `walshConjugation_cl11EquivMat_darboux` (`L1508`), and `cl11StandardEquiv_frameVector` (`L1519`).

---

## 8. `BUCKET 1 / 2 / 3` Scope Ledger, Caveats, and Errata

### 8.1 `BUCKET 1 / 2 / 3` Classification Ledger

| Item / Owner | Classification | Exact Scope, Hypotheses & Caveats |
|---|---|---|
| Base `Cl(1,1)` 3-basis reconciliation, `V₄` atom symmetry, graded Morita (`Cl11Matrix`, `Cl11GradedMorita`, `Cl11GradedTensorMorita`, `Cl11KleinFourAdjointRepresentation`) | **BUCKET 1** `[theorem_backed]` | Finite `Cl(1,1)` / `M₂(ℝ)` / `evenOdd q11 ᵍ⊗[ℝ] 𝒜` algebra, `V₄` invariance = scalars, 3-basis `AlgEquiv` table |
| Split Clifford towers, `ClTower`, `DoubleCylinderColimit`, `SplitCliffordHeisenbergTopological`, `Clifford/BottPeriodicity` | **BUCKET 1** `[theorem_backed]` | Staged `ℕ`-indexed `_root_.DirectLimit` equivalences, `DiscreteTopology` maps (`L52–68`), and split `(n,n)` step `clsplit_succ_equiv` (`Clifford/Tower.lean:65`) only (not 8-fold Bott periodicity or analytic completion on `SplitCliffordInfinity`) |
| Graded tensor chains, JW differentials, soldering boundary, Clifford tensor trains (`Cl11HomogeneousChains`, `Cl11GradedDifferential`, `SplitCliffordMatrixLimitSoldering`, `Cl11TensorTrainSynthesis`) | **BUCKET 1** `[theorem_backed]` | `gradedTensorSuccessor_not_algHom` (`L779`) proves `BondCoherence` false for naive `spinorRepresentation`; unconditional JW bit-word soldering `splitCliffordInfinityEquivLimit` and `nativeChainDifferential_nativeChain` (`prefixParity`) + `Fin.rev` duality hold cleanly |
| Coordinate-less `CliffordAlgebra Q` invariance & `ErlangenCoordinateless` (`GradedGraceContraction`, `CoordinateLessCliffordInvariance`, `CliffordSymmetryLift`, `ErlangenCoordinateless`) | **BUCKET 1 / BUCKET 2** `[theorem_backed]` | `GeneralRing` (`[CommRing R]`) identities are unconditional (`BUCKET 1`); grade projections, `O(Q)`/`SO(Q)` characterizations require `[Invertible (2 : K)]` and `[Module.Finite K M]` (`BUCKET 2`, no nondegeneracy needed); `ErlangenCoordinateless` scoped to concrete `M₂(ℂ)` Pauli identities |
| R3 ↔ R1 `FormHodgeCliffordData` coupling (`ZornDifferentialFormsCliffordBridge`) & abstract rotor/Darboux/`Spin(Q)` lifting (`CartanHestenesRotorSpinConnectionMaurerCartanSynthesis`) | **BUCKET 1 / BUCKET 2** `[theorem_backed]` | Sections 4A–4B & 4D (`L435–585, 833–1043`) hold over arbitrary `[CommRing R_coeff]`; Sections 4C & 4E require `[Invertible (2 : R_coeff)]`; `mem_cliffordGradeSubmodule_two_of_even_reverse_neg_finrank_le_three` strictly requires `Module.finrank ℝ M_real ≤ 3` (sharp via `dim = 6` 6-blade witness); §C Hodge–Dirac equivariance requires `hd`/`hs`; analytic `HasDerivAt` lives on `Mat2` (`L160`) |
| `placeholder_audit.py --strict` soft findings (4 across M2.3) | **BUCKET 1** (hygiene) | `ZornDifferentialFormsCliffordBridge`: `L110` (`hodgeStar_involutive`, decl `L111`), `L165` (`hodgeDirac_eq_add_codifferential`, decl `L166`); `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis`: `L838` (`clRotorDarbouxConnection_eq_actionThetaR`, decl `L840`), `L1049` (`variable`). Zero hard findings, zero gaps |
| `lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean` (`125` lines) | **BUCKET 3** `[conjectural_scaffold]` | Untouched in M2.3. Inspection (`L50–125`) confirms `cl11_mobius_recovers_sl2c`, `bott_step_preserves_poleForm_integral`, `bott_step_preserves_deRhamClass`, `thermal_time_functorial_bott_step`, and `buscher_duality_as_clifford_monodromy_reduction` still prove tautologies `(clsplit_succ_equiv n) = (clsplit_succ_equiv n)` / `rfl` on `moebiusAction` |
| M2.2 / M2.3 Ergonomic & Transparency Caveats | **BUCKET 2 / BUCKET 3** (API notes) | (1) `clSplitGradedTensorEquivClTower` specializes to `involutionGrading θ hθ` and `_parity` uses `private def towerParityAux`; (2) `diagV4ClsplitAuto` is not packaged as a standalone `SymmetryAction V4 (Clsplit n)`; (3) external `ClTower ℝ 1` callers should use `clSplitGradedTensorEquivClTower` / `tensorMatrixEquiv_*` rather than `GradedAlgebra (clTowerGrading ...)` vs `Matrix.algebra`; (4) `DerivationLieLane.toLieActionLane` (`DerivationExteriorCalculus.lean:735`) is `def` (requires `ActionOperatorForm K.toLieActionLane n` retyping before `rw`); (5) `pullbackFormFamily` / `cliffordAlternatingEval_cliffordGradeProj` (`ZornDifferentialFormsCliffordBridge.lean:719, 784`) bind `LieActionLane`, posing a typeclass-diamond hazard on native carriers like `Vec11`; (6) `witnessFormHodgeCliffordData` (`L188`) uses `hodgeStar := LinearMap.id` (giving `(hodgeDirac witnessFormHodgeCliffordData)² = 0`, whereas `hodgeDirac_comp_hodgeDirac` (`L179`) shows `(hodgeDirac D)² = D.differential ∘ hodgeCodifferential D + hodgeCodifferential D ∘ D.differential` can be nonzero on degree-0 elements for nontrivial `D.hodgeStar` via `FormHodgeCliffordData.hodgeStar`); (7) `evenOdd q11 0` is commutative (`thetaR` vanishes on `q11` units, non-vanishing on `Clsplit 2` `dim = 4`) |
| M3 / R4 Deferred Integrations | **BUCKET 3** (deferred) | (1) Smooth manifold rotor fields `U → Spin(Q)`; (2) standalone theorem `Function.Injective cl11V4SymmetryAction.act`; (3) `ClNNFredholmBridge` extension from `Cl(1,1)` to `Clsplit n` and `RealSplitKreinKasparovCycle.ρ` (`RealSplitKreinKasparovCycle.lean:27–30`) right-Hilbert-`B`-module upgrade; (4) barrel exports (`InfoGeometry.lean`, `AllExhaustive.lean`, `Canonical/All.lean`, `Synthesis/All.lean`) and `src/InfoGeometry/` mirror sync; (5) full `tests/reconciliation_e2e/` (`R4`) gate run |

### 8.2 Verified Errata & Citation Corrections

1. **`cl11V4SymmetryAction`**: Declared in `lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean:562` (NOT `CoordinateLessCliffordInvariance.lean`, which declares `v4ToQ11IsometryHom` at `L1025` and `cl11EquivMat_v4_equivOfIsometry` at `L1068`).
2. **`splitCliffordLift_evenOdd`**: Actual names in `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` are `splitCliffordLift_evenOdd_map` (`L220`) and `splitCliffordLift_mem_evenOdd_iff` (`L226`).
3. **`SplitSpinGroup n` path**: Declared in `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean:51` (NOT `Canonical/`).
4. **M2.1 Iteration 4 `.olean` clean declaration counts** (`m2_sub_orch_1_gen2/handoff.md`): `GradedGraceContraction.olean` (`210`), `CoordinateLessCliffordInvariance.olean` (`106`), `CliffordSymmetryLift.olean` (`77`), `ErlangenCoordinateless.olean` (`28`) — total **`421/421` clean declarations**.

---

## 9. Verification Matrix & M3 Handoff Contracts

### 9.1 Verified Gate Ledger (`M2.1`, `M2.2`, `M2.3`)

| Scope | Verification Command & Coverage | Observed Result |
|---|---|---|
| **M2.1 (`F3.4`) Iter 4 Gate** | 4-module `run_locked_lake_build.py` (`8984` jobs) + `run_locked_lean.py` (4 owners + 6 consumers) + `axiom_check.lean` (`210 + 106 + 77 + 28 = 421` decls) + Challenger 7/8 ring/degenerate/SO/diamond probes + Auditor 4 (`CLEAN`) | **PASS** (`exit 0`, `421/421` clean, `0` gaps) |
| **M2.2 (`F3.1–F3.3`) Iter 1 Gate** | 12-module `run_locked_lake_build.py` (6 M2.2 + 6 consumers, `9747` jobs) + 6/6 `run_locked_lean.py` + `axiom_check.py`/`.lean` (`102 + 180 + 323` + 3 `OK`) + 37 `#print axioms` + Challenger 1/2 probes + Auditor (`CLEAN`) | **PASS** (`exit 0`, `0` gaps, `0` traps) |
| **M2.3 (`F3.5`) Lean & Consumers** | 9-module `run_locked_lake_build.py --wait-for-build-lock` (`ZornDifferentialFormsCliffordBridge`, `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis`, + 7 downstream consumers: `ZornDifferentialFormsLaplacianBridge`, `ZornMaxwellFormsBridge`, `ZornMaxwellFormsDegreeBridge`, `CartanHestenesRotorSpinConnectionMaurerCartanSynthesisAudit`, `EmergentSpacetimeSuperchargeCartanTransactionSynthesis`, `AmplituhedronBeyondHorizonsGrandSynthesis`, `HestenesStokesAlgebraicBoundarySynthesis`) | `Build completed successfully (10150 jobs).` (`exit 0`, `0` warnings/errors) |
| **M2.3 Native Axiom Replay** | `flock -x /tmp/info-geometry-build.lock lake env lean --run tools/infra/axiom_check.lean` on both M2.3 `.olean`s + Audit file `#print axioms` | `ZornDifferentialFormsCliffordBridge.olean`: `✓ all 157 declarations clean`; `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.olean`: `✓ all 164 declarations clean` (`⊆ {propext, Classical.choice, Quot.sound}`) |
| **M2.3 Static, OpenGauss & `pytest`** | `placeholder_audit.py --strict` (`hard=0, soft=4`), `axiom_audit.py --fail-on-gaps` (`0` gaps), `detect_hollow_theorems.py --strict` (`exit 0`), `opengauss_screener.py --strict` (`0` traps), `pytest tests/test_hestenes_dirac_formalization.py -k test_cartan_hyperbolic_rotor_derivative_is_a_real_matrix_derivative` (`1 passed, 22 deselected`) | **PASS** (`exit 0`, Challenger 1 & 2 `APPROVE`, Auditor `CLEAN`) |

### 9.2 Downstream Handoff Contracts for M3 (`R2` ↔ `R3`)

M3 modules connecting `R2` (Erlangen 2.0 / Krein / Kasparov) to `R3` may import and compose:
1. **3-Basis & `ClTower` Contract**: `InfoGeometry.Clifford.Cl11GradedMorita`, `InfoGeometry.Clifford.Cl11GradedTensorMorita`, `InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis`, and `InfoGeometry.Canonical.SplitCliffordTowerUnification` (`clSplitGradedTensorEquivClTower`, `clSplitEquivClTowerReal`).
2. **Direct-Limit, `V₄`, & Graded Chain Contract**: `InfoGeometry.Canonical.SplitCliffordDirectLimit`, `InfoGeometry.Canonical.SplitCliffordHeadTailTower`, `InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation`, `InfoGeometry.Clifford.Cl11HomogeneousChains`, `InfoGeometry.Clifford.Cl11GradedDifferential` (`splitCliffordInfinityEquivLimit`, `splitJWDifferential`, `nativeChainDifferential`), and `InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering`. (Analytic C*-completions must build explicitly on `ClInfOpCompletion A`, not `SplitCliffordInfinity`.)
3. **Coordinate-Less Invariance & Hodge–Dirac Contract**: `InfoGeometry.Clifford.GradedGraceContraction`, `InfoGeometry.Clifford.CoordinateLessCliffordInvariance`, `InfoGeometry.Algebraic.CliffordSymmetryLift`, and `InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge`.
4. **Spin-Group & Rotor-Connection Contract**: `InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis` (`spinGroupToIsometryHom`, `equivOfIsometry_spinGroupToIsometryHom`, `clRotorDarboux_maurerCartan`, `clRotorDarboux_derivation_maurerCartan`, `reverseCommutingLane`, `cl11HyperbolicRotor_mem_spinGroup`).
