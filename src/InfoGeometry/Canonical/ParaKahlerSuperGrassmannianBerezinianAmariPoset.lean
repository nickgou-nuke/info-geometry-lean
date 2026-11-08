/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
import InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset
import InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinVandermondeColorPoset
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import InfoGeometry.Canonical.UnifiedDikinGeometry

/-!
# The 7-Stage Para-Kähler Super-Grassmannian & Berezinian Amari Operator Geometry Poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`)

===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBerezinianAmariPoset
Role: Canonical formalization of the 7-stage Para-Kähler Super-Grassmannian &
  Berezinian Amari Operator Geometry Poset (`𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`), bridged
  directly to the 7-stage Split-Octonion Isotropic Circular Amari–Baryon–Nambu
  Poset (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`):

1. **Rung 0, Rung 1, & Stages `𝔓₁ ≺ 𝔓₂` (Para-Kähler Tangent Polarization,
   Single-Chart Unipotent Idempotency, Socratic Linear-Superposition Aporia, &
   Two-Chart Commutator Curvature)**:
   - A point of the Super-Grassmannian is an idempotent projector `P * P = P`,
     whose real tangent space `T_P Gr = 𝔫_+ ⊕ 𝔫_-` is split by the Chiral
     DeWitt Difference Involution `S_P = 2P - 1` (`S_P² = 1`, `S_P|_{𝔫_±} = ±id`).
   - Each single unipotent chart `P_+(N_+) = (1 - N_+) P (1 + N_+) = P + N_+`
     and `P_-(N_-) = (1 + N_-) P (1 - N_-) = P + N_-` is strictly idempotent
     (`P_+² = P_+`, `P_-² = P_-`).
   - **Rung 0 Socratic Aporia**: Naive linear superposition `Ψ = P + N_+ + N_- = P + Φ`
     jumps off the Super-Grassmannian (`Ψ² - Ψ = V ≠ 0`), while the two-chart
     commutator exposes the Para-Kähler curvature `[P_+, P_-] = Σ - N_+ - N_-`.
2. **Rung 2 & Stage `𝔓₃` (Exact Bruhat-Dressed Two-Chart Idempotent & Jordan
   Triple Cancellation of the Aporia)**:
   - Conjugating the dual chart `P + N_-` by the primal unipotent exponential
     `1 ± N_+` defines the Bruhat-dressed two-chart projector
     `P̂(N_+, N_-) := (1 - N_+)(P + N_-)(1 + N_+) = P + Φ - Σ - V N_+`,
     where `V N_+ = Q_+ N_+ = N_+ Q_- = N_+ N_- N_+` is the Peirce Jordan triple
     product.
   - Proves that `P̂(N_+, N_-)² = P̂(N_+, N_-)` holds identically in any
     associative ring `[Ring B]` and preserves the Grassmannian rank
     `tr(P̂) = tr(P)` under any cyclic trace.
3. **Rung 3 & Stage `𝔓₄` (Associative Push–Pull Intertwining Law & Push–Pull
   Resolvent Identity)**:
   - Proves `Q_+^k N_+ = N_+ Q_-^k = V^k N_+` and `Q_-^k N_- = N_- Q_+^k = V^k N_-`
     for all `k : ℕ`, `(1 - Q_+) N_+ = N_+ (1 - Q_-) = (1 - V) N_+`, and the
     exact Push–Pull Resolvent Identity:
     `R_+ * N_+(dA) = N_+(dA) * R_- = R_V * N_+(dA) = N_+(dA) * R_V`
     for any tangent variation `dA : B`.
4. **Rung 4 & Stage `𝔓₅` (Legendre–Schur Differential & Hua–Bergman–Dikin
   Para-Kähler Operator Metric)**:
   - Proves the resolvent absorption identity `1 + Q_- R_- = R_-`, the exact
     collapse of the unfactored Legendre variation
     `R_+ dN_+ + R_+ dN_+ N_- R_+ N_+ = R_+ dN_+ R_- = R_V dN_+ R_V`,
     and the equality of the sheet-resolvent and total-resolvent
     **Hua–Bergman–Dikin Para-Kähler Operator Metrics**:
     `G_V(dN_+, dN_-) = R_+ dN_+ R_- dN_- = R_V dN_+ R_V dN_-`.
5. **Stages `𝔓₆ ≺ 𝔓₇` (Super-LU Berezinian Potential, Weyl–Berezinian Deformation
   Triad, Bigraded `V₄` Closure, & Unified `𝕆_s ↪ SU(6|21) ↪ Gr(m|n, p|q) ↪ Amari`
   Master Synthesis)**.

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `ParaKahlerSuperGrassmannianAmariStage`, `stageIndex_injective`, `causalEdge_lt`,
  `transGen_causalEdge_lt`, `causalEdge_acyclic`, `toRepDepth_rank_monotone`,
  `toOntologyMetaLevel_rank_monotone`, `fromSplitOctonionStage_monotone`,
  `strict_seven_stage_chain`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Stages `𝔓₁`–`𝔓₇` Bruhat-dressed two-chart idempotent, push–pull intertwining,
  Hua–Bergman–Dikin operator metric, and Super-LU Berezinian synthesis under explicit idempotent
  and resolvent hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Global analytic manifold charts on infinite-dimensional Banach super-Grassmannians remain
  outside this algebraic and finite-supermatrix scope.

## i. Overview
Formalizes the 7-stage Para-Kähler Super-Grassmannian & Berezinian Amari operator geometry poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`).

## ii. Key results
- `ParaKahlerSuperGrassmannianAmariStage.causalEdge_acyclic`
- `ParaKahlerSuperGrassmannianAmariStage.fromSplitOctonionStage_monotone`

## iii. Table of contents
- Section 1: The 7-Stage Para-Kähler Super-Grassmannian & Berezinian Amari Causal Poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`)
- Sections 2–6: Stages `𝔓₁`–`𝔓₇`

## iv. References
- L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains* (1963).
- F. A. Berezin, *Introduction to Superanalysis* (1987).
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBerezinianAmariPoset

open scoped BigOperators Matrix
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
open InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
open InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset
open InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinVandermondeColorPoset
open InfoGeometry.Supergeometry.Berezinian
open InfoGeometry.SuperGrassmannian.WeylBerezinian
open InfoGeometry.Canonical.GLSupermatrixGradedLie
open InfoGeometry.Canonical.CattoGurseyBlockGrading
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-!
## 1. The 7-Stage Para-Kähler Super-Grassmannian & Berezinian Amari Causal Poset (`𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`)
-/

/-- The 7 causal stages of the Para-Kähler Super-Grassmannian & Berezinian Amari
Operator Geometry Poset (`𝔓₁ ≺ 𝔓₂ ≺ ⋯ ≺ 𝔓₇`). -/
inductive ParaKahlerSuperGrassmannianAmariStage : Type
  | P1_ParaKahlerTangentPolarizationOfSuperGrassmannian
  | P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature
  | P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation
  | P4_AssociativePushPullIntertwiningLawAndResolventIdentity
  | P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
  | P6_SuperLUBerezinianPotentialAndBigradedV4Closure
  | P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure
  deriving DecidableEq, Repr, Inhabited

namespace ParaKahlerSuperGrassmannianAmariStage

/-- Integer rank `0..6` of the 7 Para-Kähler Super-Grassmannian Amari stages. -/
def stageIndex : ParaKahlerSuperGrassmannianAmariStage → ℕ
  | .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian => 0
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature => 1
  | .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation => 2
  | .P4_AssociativePushPullIntertwiningLawAndResolventIdentity => 3
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric => 4
  | .P6_SuperLUBerezinianPotentialAndBigradedV4Closure => 5
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure => 6

-- theorem-class: transport lemma
/-- The integer rank map `stageIndex` is injective on `ParaKahlerSuperGrassmannianAmariStage`. -/
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder ParaKahlerSuperGrassmannianAmariStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype ParaKahlerSuperGrassmannianAmariStage where
  elems := {
    .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian,
    .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature,
    .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation,
    .P4_AssociativePushPullIntertwiningLawAndResolventIdentity,
    .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric,
    .P6_SuperLUBerezinianPotentialAndBigradedV4Closure,
    .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure
  }
  complete x := by cases x <;> simp

/-- Directed causal edges `𝔓₁ → 𝔓₂ → 𝔓₃ → 𝔓₄ → (𝔓₅, 𝔓₆) → 𝔓₇`. -/
def causalEdge :
    ParaKahlerSuperGrassmannianAmariStage → ParaKahlerSuperGrassmannianAmariStage → Prop
  | .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian,
    .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature => True
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature,
    .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation => True
  | .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation,
    .P4_AssociativePushPullIntertwiningLawAndResolventIdentity => True
  | .P4_AssociativePushPullIntertwiningLawAndResolventIdentity,
    .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric => True
  | .P4_AssociativePushPullIntertwiningLawAndResolventIdentity,
    .P6_SuperLUBerezinianPotentialAndBigradedV4Closure => True
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric,
    .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure => True
  | .P6_SuperLUBerezinianPotentialAndBigradedV4Closure,
    .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
/-- Every directed causal edge strictly increases the stage order. -/
theorem causalEdge_lt {s t : ParaKahlerSuperGrassmannianAmariStage} (h : causalEdge s t) :
    s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
/-- Any transitive path of causal edges strictly increases the stage order. -/
theorem transGen_causalEdge_lt {s t : ParaKahlerSuperGrassmannianAmariStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
/-- The 7-stage `ParaKahlerSuperGrassmannianAmariStage` poset is strictly acyclic. -/
theorem causalEdge_acyclic (s : ParaKahlerSuperGrassmannianAmariStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : ParaKahlerSuperGrassmannianAmariStage → RepDepth`. -/
def toRepDepth : ParaKahlerSuperGrassmannianAmariStage → RepDepth
  | .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian => .projective
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature => .operator
  | .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation => .operator
  | .P4_AssociativePushPullIntertwiningLawAndResolventIdentity => .krein
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric => .transport
  | .P6_SuperLUBerezinianPotentialAndBigradedV4Closure => .thermo
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure => .thermo

-- theorem-class: transport lemma
/-- The representation-depth projection `toRepDepth` is monotone with respect to stage order. -/
theorem toRepDepth_rank_monotone {a b : ParaKahlerSuperGrassmannianAmariStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level classification `toOntologyMetaLevel : ParaKahlerSuperGrassmannianAmariStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : ParaKahlerSuperGrassmannianAmariStage → OntologyMetaLevel
  | .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian => .M1_ProjectorClabject
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature =>
      .M2_GrassmannianPowertypeOrbit
  | .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation =>
      .M2_GrassmannianPowertypeOrbit
  | .P4_AssociativePushPullIntertwiningLawAndResolventIdentity =>
      .M2_GrassmannianPowertypeOrbit
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric =>
      .M3_ErlangenCasimirMetaLaw
  | .P6_SuperLUBerezinianPotentialAndBigradedV4Closure =>
      .M3_ErlangenCasimirMetaLaw
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure =>
      .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
/-- The ontology meta-level projection `toOntologyMetaLevel` is monotone with respect to stage order. -/
theorem toOntologyMetaLevel_rank_monotone {a b : ParaKahlerSuperGrassmannianAmariStage}
    (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Order-preserving cross-poset map from the 7-stage Split-Octonion Isotropic Poset
(`𝔒₁ ≺ … ≺ 𝔒₇`) to the 7-stage Para-Kähler Super-Grassmannian Poset (`𝔓₁ ≺ … ≺ 𝔓₇`). -/
def fromSplitOctonionStage :
    SplitOctonionIsotropicAmariStage → ParaKahlerSuperGrassmannianAmariStage
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis =>
      .P1_ParaKahlerTangentPolarizationOfSuperGrassmannian
  | .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays =>
      .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection =>
      .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation
  | .O4_DeWittSumOperatorFisherMetric =>
      .P4_AssociativePushPullIntertwiningLawAndResolventIdentity
  | .O5_DeWittDifferenceBerrySkewnessCurvature =>
      .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
  | .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor =>
      .P6_SuperLUBerezinianPotentialAndBigradedV4Closure
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference =>
      .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure

-- theorem-class: transport lemma
/-- The cross-poset embedding `fromSplitOctonionStage` is monotone. -/
theorem fromSplitOctonionStage_monotone : Monotone fromSplitOctonionStage := by
  intro a b hab
  change SplitOctonionIsotropicAmariStage.stageIndex a ≤
    SplitOctonionIsotropicAmariStage.stageIndex b at hab
  change stageIndex (fromSplitOctonionStage a) ≤ stageIndex (fromSplitOctonionStage b)
  cases a <;> cases b <;> revert hab <;> decide

/-- Strict 7-stage chain witness and cardinality `7`. -/
theorem strict_seven_stage_chain :
    (ParaKahlerSuperGrassmannianAmariStage.P1_ParaKahlerTangentPolarizationOfSuperGrassmannian <
      .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature) ∧
    (ParaKahlerSuperGrassmannianAmariStage.P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature <
      .P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation) ∧
    (ParaKahlerSuperGrassmannianAmariStage.P3_ExactBruhatDressedTwoChartIdempotentAndJordanTripleCancellation <
      .P4_AssociativePushPullIntertwiningLawAndResolventIdentity) ∧
    (ParaKahlerSuperGrassmannianAmariStage.P4_AssociativePushPullIntertwiningLawAndResolventIdentity <
      .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric) ∧
    (ParaKahlerSuperGrassmannianAmariStage.P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric <
      .P6_SuperLUBerezinianPotentialAndBigradedV4Closure) ∧
    (ParaKahlerSuperGrassmannianAmariStage.P6_SuperLUBerezinianPotentialAndBigradedV4Closure <
      .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure) ∧
    Fintype.card ParaKahlerSuperGrassmannianAmariStage = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

end ParaKahlerSuperGrassmannianAmariStage

/-!
## 2. Stages `𝔓₁ ≺ 𝔓₂`: Para-Kähler Tangent Polarization, Single-Chart Unipotent Idempotency, Socratic Linear-Superposition Aporia, & Two-Chart Commutator Curvature
-/

section SingleAndTwoChartSuperGrassmannian

variable {B : Type*} [Ring B]

/-- Primal `e`-isotropic unipotent Super-Grassmannian chart projector
`P_+(P, A) := P + N_+(A) = (1 - N_+(A)) * P * (1 + N_+(A))`. -/
def primalSuperChartProj (P A : B) : B :=
  P + conePlus P A

/-- Dual `m`-isotropic unipotent Super-Grassmannian chart projector
`P_-(P, C) := P + N_-(C) = (1 + N_-(C)) * P * (1 - N_-(C))`. -/
def dualSuperChartProj (P C : B) : B :=
  P + coneMinus P C

/-- Naive linear two-chart superposition `Ψ(P, A, C) := P + N_+(A) + N_-(C) = P + Φ`. -/
def naiveLinearTwoChartSuperposition (P A C : B) : B :=
  P + genPhi P A C

/-- **Stages `𝔓₁` & `𝔓₂` Theorem (`p1_p2_parakahler_polarization_single_chart_idempotency_and_two_chart_commutator`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Para-Kähler Tangent Polarization (`𝔓₁`)**:
   * `invS P * invS P = 1`,
   * `invS P * conePlus P A = conePlus P A` and `conePlus P A * invS P = -conePlus P A`,
   * `invS P * coneMinus P C = -coneMinus P C` and `coneMinus P C * invS P = coneMinus P C`,
   * `conePlus P A * conePlus P A = 0` and `coneMinus P C * coneMinus P C = 0`.
2. **Single-Chart Unipotent Dressing & Idempotency (`𝔓₂`)**:
   * `unipotentExpPlusInv P A * P * unipotentExpPlus P A = primalSuperChartProj P A`,
   * `unipotentExpMinus P C * P * unipotentExpMinusInv P C = dualSuperChartProj P C`,
   * `primalSuperChartProj P A * primalSuperChartProj P A = primalSuperChartProj P A`,
   * `dualSuperChartProj P C * dualSuperChartProj P C = dualSuperChartProj P C`.
3. **Rung 0 Socratic Aporia (Naive Linear Superposition Jumps Off the Super-Grassmannian)**:
   * `naiveLinearTwoChartSuperposition P A C = P + conePlus P A + coneMinus P C`,
   * `naiveLinearTwoChartSuperposition P A C * naiveLinearTwoChartSuperposition P A C - naiveLinearTwoChartSuperposition P A C = genV P A C`.
4. **Two-Chart Para-Kähler Commutator (`𝔓₂`)**:
   * `primalSuperChartProj P A * dualSuperChartProj P C - dualSuperChartProj P C * primalSuperChartProj P A = genSig P A C - conePlus P A - coneMinus P C`,
   * `primalSuperChartProj P A * dualSuperChartProj P C - dualSuperChartProj P C * primalSuperChartProj P A = genSig P A C - genPhi P A C`. -/
theorem p1_p2_parakahler_polarization_single_chart_idempotency_and_two_chart_commutator
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    unipotentExpPlusInv P A * P * unipotentExpPlus P A = primalSuperChartProj P A ∧
    unipotentExpMinus P C * P * unipotentExpMinusInv P C = dualSuperChartProj P C ∧
    primalSuperChartProj P A * primalSuperChartProj P A = primalSuperChartProj P A ∧
    dualSuperChartProj P C * dualSuperChartProj P C = dualSuperChartProj P C ∧
    naiveLinearTwoChartSuperposition P A C = P + conePlus P A + coneMinus P C ∧
    naiveLinearTwoChartSuperposition P A C * naiveLinearTwoChartSuperposition P A C -
      naiveLinearTwoChartSuperposition P A C = genV P A C ∧
    primalSuperChartProj P A * dualSuperChartProj P C -
      dualSuperChartProj P C * primalSuperChartProj P A =
      genSig P A C - conePlus P A - coneMinus P C ∧
    primalSuperChartProj P A * dualSuperChartProj P C -
      dualSuperChartProj P C * primalSuperChartProj P A =
      genSig P A C - genPhi P A C := by
  unfold primalSuperChartProj dualSuperChartProj naiveLinearTwoChartSuperposition
    unipotentExpPlus unipotentExpPlusInv unipotentExpMinus unipotentExpMinusInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-!
## 3. Rung 2 & Stage `𝔓₃`: Exact Bruhat-Dressed Two-Chart Super-Grassmannian Idempotent & Jordan Triple Cancellation of the Aporia
-/

/-- The primal Peirce Jordan triple product `N_+(A) N_-(C) N_+(A) ∈ 𝔫_+`. -/
def peirceJordanTriplePlus (P A C : B) : B :=
  conePlus P A * coneMinus P C * conePlus P A

/-- The dual Peirce Jordan triple product `N_-(C) N_+(A) N_-(C) ∈ 𝔫_-`. -/
def peirceJordanTripleMinus (P A C : B) : B :=
  coneMinus P C * conePlus P A * coneMinus P C

/-- The Bruhat-dressed two-chart Super-Grassmannian projector
`P̂(P, A, C) := (1 - N_+(A)) * (P + N_-(C)) * (1 + N_+(A))`. -/
def dressedTwoChartProj (P A C : B) : B :=
  unipotentExpPlusInv P A * dualSuperChartProj P C * unipotentExpPlus P A

/-- The dual Bruhat-dressed two-chart Super-Grassmannian projector
`P̂_dual(P, A, C) := (1 + N_-(C)) * (P + N_+(A)) * (1 - N_-(C))`. -/
def dressedTwoChartProjDual (P A C : B) : B :=
  unipotentExpMinus P C * primalSuperChartProj P A * unipotentExpMinusInv P C

/-- The positive-sign Bruhat-dressed two-chart Super-Grassmannian projector
`P̂_+(P, A, C) := (1 + N_+(A)) * (P + N_-(C)) * (1 - N_+(A))`. -/
def dressedTwoChartProjPos (P A C : B) : B :=
  unipotentExpPlus P A * dualSuperChartProj P C * unipotentExpPlusInv P A

/-- **Stage `𝔓₃` Theorem (`p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple_cancellation`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Exact Peirce Jordan Triple Identities**:
   * `peirceJordanTriplePlus P A C = qgtPlus P A C * conePlus P A`,
   * `peirceJordanTriplePlus P A C = conePlus P A * qgtMinus P A C`,
   * `peirceJordanTriplePlus P A C = genV P A C * conePlus P A`,
   * `peirceJordanTripleMinus P A C = qgtMinus P A C * coneMinus P C`,
   * `peirceJordanTripleMinus P A C = coneMinus P C * qgtPlus P A C`,
   * `peirceJordanTripleMinus P A C = genV P A C * coneMinus P C`.
2. **Explicit Expansion of the Bruhat-Dressed Two-Chart Projectors**:
   * `unipotentExpPlusInv P A * dualSuperChartProj P C = P + coneMinus P C - qgtPlus P A C`,
   * `dressedTwoChartProj P A C = P + genPhi P A C - genSig P A C - genV P A C * conePlus P A`,
   * `dressedTwoChartProj P A C = naiveLinearTwoChartSuperposition P A C - genSig P A C - peirceJordanTriplePlus P A C`,
   * `dressedTwoChartProjDual P A C = P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C`,
   * `dressedTwoChartProjPos P A C = P - conePlus P A + coneMinus P C + genSig P A C - genV P A C * conePlus P A`.
3. **Exact Idempotency Across the Curved Manifold (`P̂² = P̂`)**:
   * `dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C`,
   * `dressedTwoChartProjDual P A C * dressedTwoChartProjDual P A C = dressedTwoChartProjDual P A C`,
   * `dressedTwoChartProjPos P A C * dressedTwoChartProjPos P A C = dressedTwoChartProjPos P A C`,
   * `(1 - dressedTwoChartProj P A C) * (1 - dressedTwoChartProj P A C) = 1 - dressedTwoChartProj P A C`.
4. **Trace / Grassmannian Rank Invariance (`tr(P̂) = tr(P)`)**:
   * For any additive trace `tr : B →+ K` satisfying `∀ X Y, tr (X * Y) = tr (Y * X)`,
     `tr (dressedTwoChartProj P A C) = tr P`. -/
theorem p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple_cancellation
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C : B) :
    peirceJordanTriplePlus P A C = qgtPlus P A C * conePlus P A ∧
    peirceJordanTriplePlus P A C = conePlus P A * qgtMinus P A C ∧
    peirceJordanTriplePlus P A C = genV P A C * conePlus P A ∧
    peirceJordanTripleMinus P A C = qgtMinus P A C * coneMinus P C ∧
    peirceJordanTripleMinus P A C = coneMinus P C * qgtPlus P A C ∧
    peirceJordanTripleMinus P A C = genV P A C * coneMinus P C ∧
    unipotentExpPlusInv P A * dualSuperChartProj P C = P + coneMinus P C - qgtPlus P A C ∧
    dressedTwoChartProj P A C =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C =
      naiveLinearTwoChartSuperposition P A C - genSig P A C - peirceJordanTriplePlus P A C ∧
    dressedTwoChartProjDual P A C =
      P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
    dressedTwoChartProjPos P A C =
      P - conePlus P A + coneMinus P C + genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    dressedTwoChartProjDual P A C * dressedTwoChartProjDual P A C = dressedTwoChartProjDual P A C ∧
    dressedTwoChartProjPos P A C * dressedTwoChartProjPos P A C = dressedTwoChartProjPos P A C ∧
    (1 - dressedTwoChartProj P A C) * (1 - dressedTwoChartProj P A C) =
      1 - dressedTwoChartProj P A C ∧
    tr (dressedTwoChartProj P A C) = tr P := by
  have hTrRank : tr (dressedTwoChartProj P A C) = tr P := by
    have hInvProd : unipotentExpPlus P A * unipotentExpPlusInv P A = 1 := by
      unfold unipotentExpPlus unipotentExpPlusInv; peirce_nf hP
    have hTrNMinus : tr (coneMinus P C) = 0 := by
      have h1 : coneMinus P C = (1 - P) * (coneMinus P C) * P := by peirce_nf hP
      have h2 : P * (1 - P) * coneMinus P C = 0 := by peirce_nf hP
      calc
        tr (coneMinus P C) = tr (((1 - P) * coneMinus P C) * P) := by rw [← h1]
        _ = tr (P * ((1 - P) * coneMinus P C)) := hCyclic ((1 - P) * coneMinus P C) P
        _ = tr (P * (1 - P) * coneMinus P C) := by rw [mul_assoc]
        _ = tr 0 := by rw [h2]
        _ = 0 := map_zero tr
    calc
      tr (dressedTwoChartProj P A C)
          = tr ((unipotentExpPlusInv P A * dualSuperChartProj P C) * unipotentExpPlus P A) := rfl
      _ = tr (unipotentExpPlus P A * (unipotentExpPlusInv P A * dualSuperChartProj P C)) :=
        hCyclic (unipotentExpPlusInv P A * dualSuperChartProj P C) (unipotentExpPlus P A)
      _ = tr ((unipotentExpPlus P A * unipotentExpPlusInv P A) * dualSuperChartProj P C) := by
        rw [mul_assoc]
      _ = tr (1 * dualSuperChartProj P C) := by rw [hInvProd]
      _ = tr (P + coneMinus P C) := by rw [one_mul]; rfl
      _ = tr P + tr (coneMinus P C) := map_add tr P (coneMinus P C)
      _ = tr P := by rw [hTrNMinus, add_zero]
  unfold peirceJordanTriplePlus peirceJordanTripleMinus dressedTwoChartProj
    dressedTwoChartProjDual dressedTwoChartProjPos dualSuperChartProj
    primalSuperChartProj naiveLinearTwoChartSuperposition
    unipotentExpPlus unipotentExpPlusInv unipotentExpMinus unipotentExpMinusInv
    qgtPlus qgtMinus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTrRank⟩ <;> peirce_nf hP

/-!
## 4. Rung 3 & Stage `𝔓₄`: Associative Push–Pull Intertwining Law (`Q_+^k N_+ = N_+ Q_-^k = V^k N_+`) & Push–Pull Resolvent Identity
-/

/-- **Stage `𝔓₄` Theorem (`p4_associative_push_pull_power_and_resolvent_intertwiner`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Base & Inductive Power Push–Pull Laws (`∀ k : ℕ`)**:
   * `qgtPlus P A C * conePlus P A = conePlus P A * qgtMinus P A C`,
   * `qgtPlus P A C * conePlus P A = genV P A C * conePlus P A`,
   * `qgtMinus P A C * coneMinus P C = coneMinus P C * qgtPlus P A C`,
   * `qgtMinus P A C * coneMinus P C = genV P A C * coneMinus P C`,
   * `qgtPlus P A C ^ k * conePlus P A = conePlus P A * (qgtMinus P A C ^ k)`,
   * `genV P A C ^ k * conePlus P A = qgtPlus P A C ^ k * conePlus P A`,
   * `qgtMinus P A C ^ k * coneMinus P C = coneMinus P C * (qgtPlus P A C ^ k)`,
   * `genV P A C ^ k * coneMinus P C = qgtMinus P A C ^ k * coneMinus P C`.
2. **Tangent-Variation Bergman Intertwining (for any `dA, dC : B`)**:
   * `(1 - genV P A C) * conePlus P dA = (1 - qgtPlus P A C) * conePlus P dA`,
   * `conePlus P dA * (1 - genV P A C) = conePlus P dA * (1 - qgtMinus P A C)`,
   * `(1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C)`,
   * `(1 - genV P A C) * coneMinus P dC = (1 - qgtMinus P A C) * coneMinus P dC`,
   * `coneMinus P dC * (1 - genV P A C) = coneMinus P dC * (1 - qgtPlus P A C)`.
3. **Exact Push–Pull Resolvent Identity (`(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ N_+`)**:
   Whenever `R_plus * (1 - qgtPlus P A C) = 1`, `(1 - qgtMinus P A C) * R_minus = 1`,
   `R_V * (1 - genV P A C) = 1`, and `(1 - genV P A C) * R_V = 1`:
   * `R_plus * conePlus P A = conePlus P A * R_minus`,
   * `R_V * conePlus P A = conePlus P A * R_V`,
   * `R_plus * conePlus P dA = R_V * conePlus P dA`,
   * `conePlus P dA * R_minus = conePlus P dA * R_V`,
   * `R_plus * conePlus P A = R_V * conePlus P A`. -/
theorem p4_associative_push_pull_power_and_resolvent_intertwiner
    {P : B} (hP : P * P = P) (A C dA dC R_plus R_minus R_V : B) (k : ℕ)
    (hR_plus_l : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus_r : (1 - qgtMinus P A C) * R_minus = 1)
    (hR_V_l : R_V * (1 - genV P A C) = 1)
    (hR_V_r : (1 - genV P A C) * R_V = 1) :
    qgtPlus P A C * conePlus P A = conePlus P A * qgtMinus P A C ∧
    qgtPlus P A C * conePlus P A = genV P A C * conePlus P A ∧
    qgtMinus P A C * coneMinus P C = coneMinus P C * qgtPlus P A C ∧
    qgtMinus P A C * coneMinus P C = genV P A C * coneMinus P C ∧
    qgtPlus P A C ^ k * conePlus P A = conePlus P A * (qgtMinus P A C ^ k) ∧
    genV P A C ^ k * conePlus P A = qgtPlus P A C ^ k * conePlus P A ∧
    qgtMinus P A C ^ k * coneMinus P C = coneMinus P C * (qgtPlus P A C ^ k) ∧
    genV P A C ^ k * coneMinus P C = qgtMinus P A C ^ k * coneMinus P C ∧
    (1 - genV P A C) * conePlus P dA = (1 - qgtPlus P A C) * conePlus P dA ∧
    conePlus P dA * (1 - genV P A C) = conePlus P dA * (1 - qgtMinus P A C) ∧
    (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) ∧
    (1 - genV P A C) * coneMinus P dC = (1 - qgtMinus P A C) * coneMinus P dC ∧
    coneMinus P dC * (1 - genV P A C) = coneMinus P dC * (1 - qgtPlus P A C) ∧
    R_plus * conePlus P A = conePlus P A * R_minus ∧
    R_V * conePlus P A = conePlus P A * R_V ∧
    R_plus * conePlus P dA = R_V * conePlus P dA ∧
    conePlus P dA * R_minus = conePlus P dA * R_V ∧
    R_plus * conePlus P A = R_V * conePlus P A := by
  have hBasePlus : qgtPlus P A C * conePlus P A = conePlus P A * qgtMinus P A C := by
    unfold qgtPlus qgtMinus; peirce_nf hP
  have hBaseVPlus : qgtPlus P A C * conePlus P A = genV P A C * conePlus P A := by
    unfold qgtPlus; peirce_nf hP
  have hBaseMinus : qgtMinus P A C * coneMinus P C = coneMinus P C * qgtPlus P A C := by
    unfold qgtPlus qgtMinus; peirce_nf hP
  have hBaseVMinus : qgtMinus P A C * coneMinus P C = genV P A C * coneMinus P C := by
    unfold qgtMinus; peirce_nf hP
  have hPowPlus : ∀ n : ℕ,
      qgtPlus P A C ^ n * conePlus P A = conePlus P A * (qgtMinus P A C ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          qgtPlus P A C ^ (n + 1) * conePlus P A
              = qgtPlus P A C ^ n * (qgtPlus P A C * conePlus P A) := by
                rw [pow_succ, mul_assoc]
          _ = (qgtPlus P A C ^ n * conePlus P A) * qgtMinus P A C := by
                rw [hBasePlus, ← mul_assoc]
          _ = conePlus P A * (qgtMinus P A C ^ (n + 1)) := by
                rw [ih, mul_assoc, ← pow_succ]
  have hPowVPlus : ∀ n : ℕ,
      genV P A C ^ n * conePlus P A = qgtPlus P A C ^ n * conePlus P A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          genV P A C ^ (n + 1) * conePlus P A
              = genV P A C ^ n * (genV P A C * conePlus P A) := by
                rw [pow_succ, mul_assoc]
          _ = genV P A C ^ n * (qgtPlus P A C * conePlus P A) := by
                rw [← hBaseVPlus]
          _ = genV P A C ^ n * (conePlus P A * qgtMinus P A C) := by
                rw [hBasePlus]
          _ = (genV P A C ^ n * conePlus P A) * qgtMinus P A C := by
                rw [← mul_assoc]
          _ = (qgtPlus P A C ^ n * conePlus P A) * qgtMinus P A C := by
                rw [ih]
          _ = qgtPlus P A C ^ n * (qgtPlus P A C * conePlus P A) := by
                rw [mul_assoc, ← hBasePlus]
          _ = qgtPlus P A C ^ (n + 1) * conePlus P A := by
                rw [← mul_assoc, ← pow_succ]
  have hPowMinus : ∀ n : ℕ,
      qgtMinus P A C ^ n * coneMinus P C = coneMinus P C * (qgtPlus P A C ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          qgtMinus P A C ^ (n + 1) * coneMinus P C
              = qgtMinus P A C ^ n * (qgtMinus P A C * coneMinus P C) := by
                rw [pow_succ, mul_assoc]
          _ = (qgtMinus P A C ^ n * coneMinus P C) * qgtPlus P A C := by
                rw [hBaseMinus, ← mul_assoc]
          _ = coneMinus P C * (qgtPlus P A C ^ (n + 1)) := by
                rw [ih, mul_assoc, ← pow_succ]
  have hPowVMinus : ∀ n : ℕ,
      genV P A C ^ n * coneMinus P C = qgtMinus P A C ^ n * coneMinus P C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          genV P A C ^ (n + 1) * coneMinus P C
              = genV P A C ^ n * (genV P A C * coneMinus P C) := by
                rw [pow_succ, mul_assoc]
          _ = genV P A C ^ n * (qgtMinus P A C * coneMinus P C) := by
                rw [← hBaseVMinus]
          _ = genV P A C ^ n * (coneMinus P C * qgtPlus P A C) := by
                rw [hBaseMinus]
          _ = (genV P A C ^ n * coneMinus P C) * qgtPlus P A C := by
                rw [← mul_assoc]
          _ = (qgtMinus P A C ^ n * coneMinus P C) * qgtPlus P A C := by
                rw [ih]
          _ = qgtMinus P A C ^ n * (qgtMinus P A C * coneMinus P C) := by
                rw [mul_assoc, ← hBaseMinus]
          _ = qgtMinus P A C ^ (n + 1) * coneMinus P C := by
                rw [← mul_assoc, ← pow_succ]
  have hBerg1 : (1 - genV P A C) * conePlus P dA = (1 - qgtPlus P A C) * conePlus P dA := by
    unfold qgtPlus; peirce_nf hP
  have hBerg2 : conePlus P dA * (1 - genV P A C) = conePlus P dA * (1 - qgtMinus P A C) := by
    unfold qgtMinus; peirce_nf hP
  have hBerg3 : (1 - qgtPlus P A C) * conePlus P A = conePlus P A * (1 - qgtMinus P A C) := by
    unfold qgtPlus qgtMinus; peirce_nf hP
  have hBerg4 : (1 - genV P A C) * coneMinus P dC = (1 - qgtMinus P A C) * coneMinus P dC := by
    unfold qgtMinus; peirce_nf hP
  have hBerg5 : coneMinus P dC * (1 - genV P A C) = coneMinus P dC * (1 - qgtPlus P A C) := by
    unfold qgtPlus; peirce_nf hP
  have hResPP : R_plus * conePlus P A = conePlus P A * R_minus := by
    calc
      R_plus * conePlus P A
          = R_plus * conePlus P A * ((1 - qgtMinus P A C) * R_minus) := by
            rw [hR_minus_r, mul_one]
      _ = R_plus * (conePlus P A * (1 - qgtMinus P A C)) * R_minus := by noncomm_ring
      _ = R_plus * ((1 - qgtPlus P A C) * conePlus P A) * R_minus := by rw [← hBerg3]
      _ = (R_plus * (1 - qgtPlus P A C)) * conePlus P A * R_minus := by noncomm_ring
      _ = conePlus P A * R_minus := by rw [hR_plus_l, one_mul]
  have h1mVCommPlus : (1 - genV P A C) * conePlus P A = conePlus P A * (1 - genV P A C) := by
    peirce_nf hP
  have hRVCommPlus : R_V * conePlus P A = conePlus P A * R_V := by
    calc
      R_V * conePlus P A
          = R_V * conePlus P A * ((1 - genV P A C) * R_V) := by rw [hR_V_r, mul_one]
      _ = R_V * (conePlus P A * (1 - genV P A C)) * R_V := by noncomm_ring
      _ = R_V * ((1 - genV P A C) * conePlus P A) * R_V := by rw [← h1mVCommPlus]
      _ = (R_V * (1 - genV P A C)) * conePlus P A * R_V := by noncomm_ring
      _ = conePlus P A * R_V := by rw [hR_V_l, one_mul]
  have h1mVCommP : P * (1 - genV P A C) = (1 - genV P A C) * P := by peirce_nf hP
  have hRVP : P * R_V = R_V * P := by
    calc
      P * R_V = (R_V * (1 - genV P A C)) * P * R_V := by rw [hR_V_l, one_mul]
      _ = R_V * ((1 - genV P A C) * P) * R_V := by noncomm_ring
      _ = R_V * (P * (1 - genV P A C)) * R_V := by rw [← h1mVCommP]
      _ = R_V * P * ((1 - genV P A C) * R_V) := by noncomm_ring
      _ = R_V * P := by rw [hR_V_r, mul_one]
  have hQM_P : qgtMinus P A C * P = 0 := by unfold qgtMinus; peirce_nf hP
  have hP_dA : P * conePlus P dA = conePlus P dA := by peirce_nf hP
  have hQM_RV_dA : qgtMinus P A C * R_V * conePlus P dA = 0 := by
    calc
      qgtMinus P A C * R_V * conePlus P dA
          = qgtMinus P A C * R_V * (P * conePlus P dA) := by rw [hP_dA]
      _ = qgtMinus P A C * (R_V * P) * conePlus P dA := by noncomm_ring
      _ = (qgtMinus P A C * P) * R_V * conePlus P dA := by rw [← hRVP]; noncomm_ring
      _ = 0 := by rw [hQM_P, zero_mul, zero_mul]
  have h1mQP_RV_dA : (1 - qgtPlus P A C) * R_V * conePlus P dA = conePlus P dA := by
    have hSplit : 1 - qgtPlus P A C = (1 - genV P A C) + qgtMinus P A C := by
      unfold qgtPlus qgtMinus; peirce_nf hP
    calc
      (1 - qgtPlus P A C) * R_V * conePlus P dA
          = ((1 - genV P A C) + qgtMinus P A C) * R_V * conePlus P dA := by rw [hSplit]
      _ = ((1 - genV P A C) * R_V) * conePlus P dA + qgtMinus P A C * R_V * conePlus P dA := by
            noncomm_ring
      _ = conePlus P dA := by rw [hR_V_r, one_mul, hQM_RV_dA, add_zero]
  have hRplus_eq_RV_dA : R_plus * conePlus P dA = R_V * conePlus P dA := by
    calc
      R_plus * conePlus P dA
          = R_plus * ((1 - qgtPlus P A C) * R_V * conePlus P dA) := by rw [h1mQP_RV_dA]
      _ = (R_plus * (1 - qgtPlus P A C)) * R_V * conePlus P dA := by noncomm_ring
      _ = R_V * conePlus P dA := by rw [hR_plus_l, one_mul]
  have h1mP_QP : (1 - P) * qgtPlus P A C = 0 := by unfold qgtPlus; peirce_nf hP
  have hdA_1mP : conePlus P dA * (1 - P) = conePlus P dA := by peirce_nf hP
  have hRV_1mP : (1 - P) * R_V = R_V * (1 - P) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hRVP]
  have hdA_RV_QP : conePlus P dA * R_V * qgtPlus P A C = 0 := by
    calc
      conePlus P dA * R_V * qgtPlus P A C
          = (conePlus P dA * (1 - P)) * R_V * qgtPlus P A C := by rw [hdA_1mP]
      _ = conePlus P dA * ((1 - P) * R_V) * qgtPlus P A C := by noncomm_ring
      _ = conePlus P dA * R_V * ((1 - P) * qgtPlus P A C) := by rw [hRV_1mP]; noncomm_ring
      _ = 0 := by rw [h1mP_QP, mul_zero]
  have hdA_RV_1mQM : conePlus P dA * R_V * (1 - qgtMinus P A C) = conePlus P dA := by
    have hSplit : 1 - qgtMinus P A C = (1 - genV P A C) + qgtPlus P A C := by
      unfold qgtPlus qgtMinus; peirce_nf hP
    calc
      conePlus P dA * R_V * (1 - qgtMinus P A C)
          = conePlus P dA * R_V * ((1 - genV P A C) + qgtPlus P A C) := by rw [hSplit]
      _ = conePlus P dA * (R_V * (1 - genV P A C)) + conePlus P dA * R_V * qgtPlus P A C := by
            noncomm_ring
      _ = conePlus P dA := by rw [hR_V_l, mul_one, hdA_RV_QP, add_zero]
  have hdA_Rminus_eq_RV : conePlus P dA * R_minus = conePlus P dA * R_V := by
    calc
      conePlus P dA * R_minus
          = (conePlus P dA * R_V * (1 - qgtMinus P A C)) * R_minus := by rw [hdA_RV_1mQM]
      _ = conePlus P dA * R_V * ((1 - qgtMinus P A C) * R_minus) := by noncomm_ring
      _ = conePlus P dA * R_V := by rw [hR_minus_r, mul_one]
  have hRplus_eq_RV_A : R_plus * conePlus P A = R_V * conePlus P A := by
    have hBergA : (1 - genV P A C) * conePlus P A = (1 - qgtPlus P A C) * conePlus P A := by
      unfold qgtPlus; peirce_nf hP
    calc
      R_plus * conePlus P A = conePlus P A * R_minus := hResPP
      _ = (R_V * (1 - genV P A C)) * conePlus P A * R_minus := by rw [hR_V_l, one_mul]
      _ = R_V * ((1 - genV P A C) * conePlus P A) * R_minus := by noncomm_ring
      _ = R_V * ((1 - qgtPlus P A C) * conePlus P A) * R_minus := by rw [hBergA]
      _ = R_V * (conePlus P A * (1 - qgtMinus P A C)) * R_minus := by rw [hBerg3]
      _ = R_V * conePlus P A * ((1 - qgtMinus P A C) * R_minus) := by noncomm_ring
      _ = R_V * conePlus P A := by rw [hR_minus_r, mul_one]
  exact ⟨hBasePlus, hBaseVPlus, hBaseMinus, hBaseVMinus,
    hPowPlus k, hPowVPlus k, hPowMinus k, hPowVMinus k,
    hBerg1, hBerg2, hBerg3, hBerg4, hBerg5,
    hResPP, hRVCommPlus, hRplus_eq_RV_dA, hdA_Rminus_eq_RV, hRplus_eq_RV_A⟩

/-!
## 5. Rung 4 & Stage `𝔓₅`: Legendre–Schur Differential & Hua–Bergman–Dikin Para-Kähler Operator Metric
-/

/-- The Legendre–Schur expectation coordinate `η_-(R_+, P, A) := R_+ * N_+(A)`. -/
def legendreSchurCoordPlus (R_plus P A : B) : B :=
  R_plus * conePlus P A

/-- The unfactored first-order Legendre variation along `dN_+ = conePlus P dA`:
`dη_- = R_+ dN_+ + R_+ dN_+ N_- R_+ N_+`. -/
def legendreVariationUnfactored (R_plus P A C dA : B) : B :=
  R_plus * conePlus P dA +
    R_plus * conePlus P dA * coneMinus P C * R_plus * conePlus P A

/-- The factored first-order Legendre–Schur differential `dη_- = R_+ dN_+ R_-`. -/
def legendreVariationFactored (R_plus R_minus P dA : B) : B :=
  R_plus * conePlus P dA * R_minus

/-- The sheet-resolvent **Hua–Bergman–Dikin Para-Kähler Operator Metric Tensor**
`G_V(dN_+, dN_-) := R_+ dN_+ R_- dN_-`. -/
def huaBergmanDikinMetric (R_plus R_minus P dA dC : B) : B :=
  R_plus * conePlus P dA * R_minus * coneMinus P dC

/-- The total-resolvent **Hua–Bergman–Dikin Para-Kähler Operator Metric Tensor**
`G_V^total(dN_+, dN_-) := R_V dN_+ R_V dN_-`. -/
def huaBergmanDikinTotalMetric (R_V P dA dC : B) : B :=
  R_V * conePlus P dA * R_V * coneMinus P dC

/-- **Stage `𝔓₅` Theorem (`p5_legendre_schur_differential_and_hua_bergman_dikin_metric`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P` and inverses
`R_plus * (1 - qgtPlus P A C) = 1`, `(1 - qgtMinus P A C) * R_minus = 1`,
`R_V * (1 - genV P A C) = 1`, `(1 - genV P A C) * R_V = 1`:
1. **Resolvent Absorption Law**:
   * `1 + qgtMinus P A C * R_minus = R_minus`.
2. **Exact Collapse of the Unfactored Legendre Variation into the Factored Differential**:
   * `legendreVariationUnfactored R_plus P A C dA = legendreVariationFactored R_plus R_minus P dA`,
   * `legendreVariationFactored R_plus R_minus P dA = R_V * conePlus P dA * R_V`.
3. **Exact Equality of the Sheet-Resolvent and Total-Resolvent Hua–Bergman–Dikin Metrics**:
   * `huaBergmanDikinMetric R_plus R_minus P dA dC = (legendreVariationUnfactored R_plus P A C dA) * coneMinus P dC`,
   * `huaBergmanDikinMetric R_plus R_minus P dA dC = huaBergmanDikinTotalMetric R_V P dA dC`,
   * `P * huaBergmanDikinTotalMetric R_V P dA dC * P = huaBergmanDikinTotalMetric R_V P dA dC`
     and `(1 - P) * huaBergmanDikinTotalMetric R_V P dA dC = 0` (the Hua–Bergman–Dikin metric
     lives purely in the upper stabilizer block `P B P`).
4. **Flat-Origin Reduction (`V = 0`, `R_+ = R_- = R_V = 1`)**:
   * `huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC`,
   * `(2 : ℤ) • huaBergmanDikinMetric 1 1 P dA dC = genV P dA dC + genSig P dA dC`. -/
theorem p5_legendre_schur_differential_and_hua_bergman_dikin_metric
    {P : B} (hP : P * P = P) (A C dA dC R_plus R_minus R_V : B)
    (hR_plus_l : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus_r : (1 - qgtMinus P A C) * R_minus = 1)
    (hR_V_l : R_V * (1 - genV P A C) = 1)
    (hR_V_r : (1 - genV P A C) * R_V = 1) :
    1 + qgtMinus P A C * R_minus = R_minus ∧
    legendreVariationUnfactored R_plus P A C dA =
      legendreVariationFactored R_plus R_minus P dA ∧
    legendreVariationFactored R_plus R_minus P dA = R_V * conePlus P dA * R_V ∧
    huaBergmanDikinMetric R_plus R_minus P dA dC =
      (legendreVariationUnfactored R_plus P A C dA) * coneMinus P dC ∧
    huaBergmanDikinMetric R_plus R_minus P dA dC =
      huaBergmanDikinTotalMetric R_V P dA dC ∧
    P * huaBergmanDikinTotalMetric R_V P dA dC * P =
      huaBergmanDikinTotalMetric R_V P dA dC ∧
    (1 - P) * huaBergmanDikinTotalMetric R_V P dA dC = 0 ∧
    huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC ∧
    (2 : ℤ) • huaBergmanDikinMetric 1 1 P dA dC = genV P dA dC + genSig P dA dC := by
  have hP4 := p4_associative_push_pull_power_and_resolvent_intertwiner
    hP A C dA dC R_plus R_minus R_V 1 hR_plus_l hR_minus_r hR_V_l hR_V_r
  have hPP : R_plus * conePlus P A = conePlus P A * R_minus := hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRplus_dA : R_plus * conePlus P dA = R_V * conePlus P dA :=
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdA_Rminus : conePlus P dA * R_minus = conePlus P dA * R_V :=
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAbsorb : 1 + qgtMinus P A C * R_minus = R_minus := by
    calc
      1 + qgtMinus P A C * R_minus
          = (1 - qgtMinus P A C) * R_minus + qgtMinus P A C * R_minus := by rw [hR_minus_r]
      _ = R_minus := by noncomm_ring
  have hVarCollapse :
      legendreVariationUnfactored R_plus P A C dA =
        legendreVariationFactored R_plus R_minus P dA := by
    calc
      legendreVariationUnfactored R_plus P A C dA
          = R_plus * conePlus P dA +
              R_plus * conePlus P dA * coneMinus P C * (R_plus * conePlus P A) := by
            unfold legendreVariationUnfactored; noncomm_ring
      _ = R_plus * conePlus P dA +
              R_plus * conePlus P dA * coneMinus P C * (conePlus P A * R_minus) := by
            rw [hPP]
      _ = R_plus * conePlus P dA * (1 + (coneMinus P C * conePlus P A) * R_minus) := by
            noncomm_ring
      _ = R_plus * conePlus P dA * (1 + qgtMinus P A C * R_minus) := rfl
      _ = legendreVariationFactored R_plus R_minus P dA := by
            rw [hAbsorb]; rfl
  have hVarRV :
      legendreVariationFactored R_plus R_minus P dA = R_V * conePlus P dA * R_V := by
    unfold legendreVariationFactored
    rw [hRplus_dA, mul_assoc, hdA_Rminus, ← mul_assoc]
  have hMetricUnfac :
      huaBergmanDikinMetric R_plus R_minus P dA dC =
        (legendreVariationUnfactored R_plus P A C dA) * coneMinus P dC := by
    rw [hVarCollapse]
    rfl
  have hMetricTotal :
      huaBergmanDikinMetric R_plus R_minus P dA dC =
        huaBergmanDikinTotalMetric R_V P dA dC := by
    change legendreVariationFactored R_plus R_minus P dA * coneMinus P dC =
      (R_V * conePlus P dA * R_V) * coneMinus P dC
    rw [hVarRV]
  have h1mVCommP : P * (1 - genV P A C) = (1 - genV P A C) * P := by peirce_nf hP
  have hRVP : P * R_V = R_V * P := by
    calc
      P * R_V = (R_V * (1 - genV P A C)) * P * R_V := by rw [hR_V_l, one_mul]
      _ = R_V * ((1 - genV P A C) * P) * R_V := by noncomm_ring
      _ = R_V * (P * (1 - genV P A C)) * R_V := by rw [← h1mVCommP]
      _ = R_V * P * ((1 - genV P A C) * R_V) := by noncomm_ring
      _ = R_V * P := by rw [hR_V_r, mul_one]
  have hP_dA : P * conePlus P dA = conePlus P dA := by peirce_nf hP
  have hdC_P : coneMinus P dC * P = coneMinus P dC := by peirce_nf hP
  have hP_Total_P :
      P * huaBergmanDikinTotalMetric R_V P dA dC * P =
        huaBergmanDikinTotalMetric R_V P dA dC := by
    unfold huaBergmanDikinTotalMetric
    calc
      P * (R_V * conePlus P dA * R_V * coneMinus P dC) * P
          = (P * R_V) * conePlus P dA * R_V * (coneMinus P dC * P) := by noncomm_ring
      _ = R_V * (P * conePlus P dA) * R_V * coneMinus P dC := by
            rw [hRVP, hdC_P]; noncomm_ring
      _ = R_V * conePlus P dA * R_V * coneMinus P dC := by rw [hP_dA]
  have h1mP_dA : (1 - P) * conePlus P dA = 0 := by peirce_nf hP
  have h1mP_RV : (1 - P) * R_V = R_V * (1 - P) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hRVP]
  have h1mP_Total :
      (1 - P) * huaBergmanDikinTotalMetric R_V P dA dC = 0 := by
    unfold huaBergmanDikinTotalMetric
    calc
      (1 - P) * (R_V * conePlus P dA * R_V * coneMinus P dC)
          = ((1 - P) * R_V) * conePlus P dA * R_V * coneMinus P dC := by noncomm_ring
      _ = R_V * ((1 - P) * conePlus P dA) * R_V * coneMinus P dC := by
            rw [h1mP_RV]; noncomm_ring
      _ = 0 := by rw [h1mP_dA, mul_zero, zero_mul, zero_mul]
  have hOrigin1 : huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC := by
    unfold huaBergmanDikinMetric qgtPlus
    simp
  have hOrigin2 :
      (2 : ℤ) • huaBergmanDikinMetric 1 1 P dA dC = genV P dA dC + genSig P dA dC := by
    rw [hOrigin1]
    unfold qgtPlus; peirce_nf hP
  exact ⟨hAbsorb, hVarCollapse, hVarRV, hMetricUnfac, hMetricTotal,
    hP_Total_P, h1mP_Total, hOrigin1, hOrigin2⟩

/-- The non-commutative Operator Möbius denominator `a + b * f` for a `2 × 2` block transformation
with upper row `(a, b)` acting on a graph coordinate `f`. -/
def operatorMoebiusDenom (a b f : B) : B :=
  a + b * f

/-- The non-commutative Operator Möbius fractional transformation `(c + d * f) * invDenom`
for a `2 × 2` block transformation `[[a, b], [c, d]]` acting on `f` with right-inverse
`invDenom` of `a + b * f`. -/
def operatorMoebiusTransform (c d f invDenom : B) : B :=
  (c + d * f) * invDenom

/-- **Global Operator Möbius = Local Push–Pull Legendre Expectation Bridge
(`p5_operator_moebius_unipotent_transition_eq_push_pull_legendre`)**:
Specializing the global Operator Möbius transition `(c + d f)(a + b f)⁻¹` to the unipotent
dual-sheet gauge transformation `a = 1`, `b = -N_-(C)`, `c = 0`, `d = 1` acting on the
primal natural coordinate `f = N_+(A)` recovers the exact local Push–Pull Legendre–Schur
expectation coordinate and its factored differential:
1. `operatorMoebiusDenom 1 (-coneMinus P C) (conePlus P A) = 1 - qgtMinus P A C`,
2. `operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_minus`,
3. `operatorMoebiusTransform 0 1 (conePlus P A) R_minus = legendreSchurCoordPlus R_plus P A`,
4. `operatorMoebiusTransform 0 1 (conePlus P A) R_minus = R_V * conePlus P A`,
5. `operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_V`,
6. `legendreVariationUnfactored R_plus P A C dA = R_plus * conePlus P dA * R_minus`,
7. `legendreVariationUnfactored R_plus P A C dA = R_V * conePlus P dA * R_V`. -/
theorem p5_operator_moebius_unipotent_transition_eq_push_pull_legendre
    {P : B} (hP : P * P = P) (A C dA dC R_plus R_minus R_V : B)
    (hR_plus_l : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus_r : (1 - qgtMinus P A C) * R_minus = 1)
    (hR_V_l : R_V * (1 - genV P A C) = 1)
    (hR_V_r : (1 - genV P A C) * R_V = 1) :
    operatorMoebiusDenom 1 (-coneMinus P C) (conePlus P A) = 1 - qgtMinus P A C ∧
    operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_minus ∧
    operatorMoebiusTransform 0 1 (conePlus P A) R_minus = legendreSchurCoordPlus R_plus P A ∧
    operatorMoebiusTransform 0 1 (conePlus P A) R_minus = R_V * conePlus P A ∧
    operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_V ∧
    legendreVariationUnfactored R_plus P A C dA = R_plus * conePlus P dA * R_minus ∧
    legendreVariationUnfactored R_plus P A C dA = R_V * conePlus P dA * R_V := by
  have hP4 := p4_associative_push_pull_power_and_resolvent_intertwiner
    hP A C dA dC R_plus R_minus R_V 1 hR_plus_l hR_minus_r hR_V_l hR_V_r
  have hP5 := p5_legendre_schur_differential_and_hua_bergman_dikin_metric
    hP A C dA dC R_plus R_minus R_V hR_plus_l hR_minus_r hR_V_l hR_V_r
  have hPP : R_plus * conePlus P A = conePlus P A * R_minus := hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRVComm : R_V * conePlus P A = conePlus P A * R_V := hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRplusRV : R_plus * conePlus P A = R_V * conePlus P A :=
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hDenom : operatorMoebiusDenom 1 (-coneMinus P C) (conePlus P A) = 1 - qgtMinus P A C := by
    unfold operatorMoebiusDenom qgtMinus
    noncomm_ring
  have hTrans : operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_minus := by
    unfold operatorMoebiusTransform
    simp
  have hLeg :
      operatorMoebiusTransform 0 1 (conePlus P A) R_minus = legendreSchurCoordPlus R_plus P A := by
    rw [hTrans]
    exact hPP.symm
  have hRV_l :
      operatorMoebiusTransform 0 1 (conePlus P A) R_minus = R_V * conePlus P A := by
    rw [hTrans, ← hPP, hRplusRV]
  have hRV_r :
      operatorMoebiusTransform 0 1 (conePlus P A) R_minus = conePlus P A * R_V := by
    rw [hRV_l, hRVComm]
  exact ⟨hDenom, hTrans, hLeg, hRV_l, hRV_r, hP5.2.1, hP5.2.1.trans hP5.2.2.1⟩

end SingleAndTwoChartSuperGrassmannian

/-!
## 6. Stage `𝔓₆`: Super-LU Berezinian Potential, Weyl–Berezinian Deformation Triad, & Bigraded `V₄ = ℤ₂^(Peirce S_P) × ℤ₂^(SUSY Γ_F)` Closure
-/

/-- **Stage `𝔓₆` Theorem (`p6_super_lu_berezinian_weyl_deformation_and_bigraded_v4_closure`)**:
Unifies the Super-LU Berezinian factorization (`BerezinianDecomposition.lean`), the
Weyl–Berezinian deformation triad (`WeylBerezinianDeformation.lean`), the Catto–Gürsey
`gl(6|21)` Bose–Fermi supertrace (`GLSupermatrixGradedLie.lean`), and the higher-moment
Chiral Supertrace recovery (`AmariBerezinianModularColimitAnalyticClosurePoset.lean`):
1. **Super-LU Factorization (`L * H * R = M`)**:
   * `factorL M_ber invD * factorH M_ber invD * factorR M_ber invD = M_ber` whenever `M_ber 1 1 * invD = 1`.
2. **Weyl–Berezinian Deformation Triad (`STr(S + X + V) = (p - q) * σ`)**:
   * `evenPart M_ber + oddPart M_ber = M_ber`,
   * `superTrace (oddPart M_ber) = 0`,
   * `superTrace (scaleOperator p_s q_s σ_s + chiralOperator k₁ k₂ + volumeOperator a_v) = (p_s - q_s) * σ_s`,
   * `superTrace (chiralOperator k₁ k₂ * chiralOperator k₁ k₂) = 0`.
3. **Catto–Gürsey `gl(6|21)` Supertrace & Chiral Supertrace Moment Recovery**:
   * `supertrace (1 : SuperMatrix 6 21 R) = -15`,
   * For all `k : ℕ`, `chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0` and
     `chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1))`. -/
theorem p6_super_lu_berezinian_weyl_deformation_and_bigraded_v4_closure
    {B : Type*} [Ring B] {K : Type*} [AddCommGroup K]
    (tr : B →+ K) (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ)
    {R : Type*} [CommRing R]
    (M_ber : Matrix (Fin 2) (Fin 2) R) (invD : R) (hD : M_ber 1 1 * invD = 1)
    (p_s q_s σ_s k₁ k₂ a_v : R) :
    factorL M_ber invD * factorH M_ber invD * factorR M_ber invD = M_ber ∧
    evenPart M_ber + oddPart M_ber = M_ber ∧
    superTrace (oddPart M_ber) = 0 ∧
    superTrace (scaleOperator p_s q_s σ_s + chiralOperator k₁ k₂ + volumeOperator a_v) =
      (p_s - q_s) * σ_s ∧
    superTrace (chiralOperator k₁ k₂ * chiralOperator k₁ k₂) = 0 ∧
    supertrace (1 : SuperMatrix 6 21 R) = -15 ∧
    chiralSupertrace tr P (genV P A C ^ (k + 1)) = 0 ∧
    chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1)) := by
  have hX2 := x2_chiral_supertrace_berezinian_moment_hierarchy tr hCyclic hP A C k
  exact ⟨super_lu_factorization M_ber invD hD,
    even_add_odd M_ber,
    superTrace_odd M_ber,
    total_deformation_superTrace p_s q_s σ_s k₁ k₂ a_v,
    superTrace_chiral_square k₁ k₂,
    supertrace_identity_6_21,
    hX2.2.2.2.2.2.1,
    hX2.2.2.2.2.2.2.2.1⟩

/-!
## 7. Stage `𝔓₇`: Master Synthesis Uniting Split-Octonion Isotropic Basis (`𝔒₁ ≺ … ≺ 𝔒₇`) with Para-Kähler Super-Grassmannian & Berezinian Amari Geometry (`𝔓₁ ≺ … ≺ 𝔓₇`)
-/

/-- **Master Synthesis Theorem (`parakahler_super_grassmannian_berezinian_amari_master_synthesis`)**:
Unifies the 7-stage Split-Octonion Isotropic Circular Amari–Baryon–Nambu Poset
(`𝔒₁ ≺ … ≺ 𝔒₇`) with the 7-stage Para-Kähler Super-Grassmannian & Berezinian Amari
Operator Geometry Poset (`𝔓₁ ≺ … ≺ 𝔓₇`):
1. Strict acyclicity and cardinality `7` of both `SplitOctonionIsotropicAmariStage` and
   `ParaKahlerSuperGrassmannianAmariStage`, plus monotonicity of `fromSplitOctonionStage`,
2. Split-Octonion `𝕆_s` circular isotropic Witt basis (`psiPlus x * psiPlus x = 0`,
   `psiPlus x_r * psiPlus y_r = psiMinus (Vec3.cross x_r y_r)`), Amari–Chentsov cubic
   baryon tensor (`det(z_k, x_k, y_k) I`), and non-commutative Nambu associator on the
   DeWitt Difference (`zornAssociator (psiPlus u_r) (psiPlus u_r) (psiPlus u_r) =
   -(scalarZorn (nambu3 u_r) * gamma5)`),
3. Single-chart unipotent idempotency (`primalSuperChartProj² = primalSuperChartProj`),
   two-chart commutator (`[P_+, P_-] = Σ - Φ`), and the exact Bruhat-dressed two-chart
   Super-Grassmannian idempotent (`dressedTwoChartProj P A C = P + Φ - Σ - V N_+`,
   `dressedTwoChartProj² = dressedTwoChartProj`, `tr(dressedTwoChartProj) = tr(P)`),
4. Push–Pull power intertwining (`Q_+^k N_+ = N_+ Q_-^k = V^k N_+`) and Push–Pull resolvent
   intertwining (`R_+ N_+ = N_+ R_- = R_V N_+`),
5. Exact factorization of the Legendre–Schur differential (`legendreVariationUnfactored =
   legendreVariationFactored = R_V dN_+ R_V`) and the Hua–Bergman–Dikin Para-Kähler metric
   (`huaBergmanDikinMetric R_plus R_minus P dA dC = huaBergmanDikinTotalMetric R_V P dA dC`),
6. Super-LU Berezinian factorization (`factorL * factorH * factorR = M_ber`), Weyl–Berezinian
   deformation splitting (`STr(S + X + V) = (p - q) * σ`), `gl(6|21)` supertrace `-15`, and
   higher-moment Chiral Supertrace recovery. -/
theorem parakahler_super_grassmannian_berezinian_amari_master_synthesis
    {B : Type*} [Ring B] {K_tr : Type*} [AddCommGroup K_tr]
    (tr : B →+ K_tr) (hCyclic : ∀ X Y : B, tr (X * Y) = tr (Y * X))
    {P : B} (hP : P * P = P) (A C dA dC R_plus R_minus R_V : B) (k : ℕ)
    (hR_plus_l : R_plus * (1 - qgtPlus P A C) = 1)
    (hR_minus_r : (1 - qgtMinus P A C) * R_minus = 1)
    (hR_V_l : R_V * (1 - genV P A C) = 1)
    (hR_V_r : (1 - genV P A C) * R_V = 1)
    {R : Type*} [Ring R]
    (u_r v_r : ZornNambuDeRhamDiracKahlerPoset.Vec3 R)
    {K : Type*} [CommRing K] (xk yk zk : ColorVec3 K) (t₁ t₂ : K)
    (M_ber : Matrix (Fin 2) (Fin 2) K) (invD : K) (hD : M_ber 1 1 * invD = 1)
    (p_s q_s σ_s k₁ k₂ a_v : K) :
    (∀ s : SplitOctonionIsotropicAmariStage,
      ¬ Relation.TransGen SplitOctonionIsotropicAmariStage.causalEdge s s) ∧
    (∀ p : ParaKahlerSuperGrassmannianAmariStage,
      ¬ Relation.TransGen ParaKahlerSuperGrassmannianAmariStage.causalEdge p p) ∧
    Monotone ParaKahlerSuperGrassmannianAmariStage.fromSplitOctonionStage ∧
    Fintype.card ParaKahlerSuperGrassmannianAmariStage = 7 ∧
    ZornAlgebra.anticommutator (ZornAlgebra.quarkU xk) (ZornAlgebra.quarkU yk) =
      ZornAlgebra.zero ∧
    ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u_r *
      ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus v_r =
      ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiMinus
        (ZornNambuDeRhamDiracKahlerPoset.Vec3.cross u_r v_r) ∧
    amariChentsovBaryon xk yk zk =
      ZornAlgebra.smul (ColorVec3.baryonDet xk yk zk) ZornAlgebra.one ∧
    ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.cubicAssociator
        (ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.psiPlus u_r) =
      -(scalarZorn (ZornNambuDeRhamDiracKahlerPoset.Vec3.nambu3 u_r) *
        ZornNambuDeRhamDiracKahlerPoset.ZornMatrix.gamma5) ∧
    primalSuperChartProj P A * primalSuperChartProj P A = primalSuperChartProj P A ∧
    primalSuperChartProj P A * dualSuperChartProj P C -
      dualSuperChartProj P C * primalSuperChartProj P A =
      genSig P A C - genPhi P A C ∧
    dressedTwoChartProj P A C =
      P + genPhi P A C - genSig P A C - genV P A C * conePlus P A ∧
    dressedTwoChartProj P A C * dressedTwoChartProj P A C = dressedTwoChartProj P A C ∧
    tr (dressedTwoChartProj P A C) = tr P ∧
    qgtPlus P A C ^ k * conePlus P A = conePlus P A * (qgtMinus P A C ^ k) ∧
    R_plus * conePlus P A = conePlus P A * R_minus ∧
    R_plus * conePlus P A = R_V * conePlus P A ∧
    legendreVariationUnfactored R_plus P A C dA =
      legendreVariationFactored R_plus R_minus P dA ∧
    huaBergmanDikinMetric R_plus R_minus P dA dC =
      huaBergmanDikinTotalMetric R_V P dA dC ∧
    factorL M_ber invD * factorH M_ber invD * factorR M_ber invD = M_ber ∧
    superTrace (scaleOperator p_s q_s σ_s + chiralOperator k₁ k₂ + volumeOperator a_v) =
      (p_s - q_s) * σ_s ∧
    supertrace (1 : SuperMatrix 6 21 K) = -15 ∧
    chiralSupertrace tr P (genSig P A C * (genV P A C ^ k)) = tr (genV P A C ^ (k + 1)) := by
  have hO := split_octonion_isotropic_circular_amari_baryon_nambu_master_poset
    u_r v_r xk yk zk t₁ t₂
  have hP12 := p1_p2_parakahler_polarization_single_chart_idempotency_and_two_chart_commutator
    hP A C
  have hP3 := p3_bruhat_dressed_two_chart_idempotent_and_jordan_triple_cancellation
    tr hCyclic hP A C
  have hP4 := p4_associative_push_pull_power_and_resolvent_intertwiner
    hP A C dA dC R_plus R_minus R_V k hR_plus_l hR_minus_r hR_V_l hR_V_r
  have hP5 := p5_legendre_schur_differential_and_hua_bergman_dikin_metric
    hP A C dA dC R_plus R_minus R_V hR_plus_l hR_minus_r hR_V_l hR_V_r
  have hP6 := p6_super_lu_berezinian_weyl_deformation_and_bigraded_v4_closure
    tr hCyclic hP A C k M_ber invD hD p_s q_s σ_s k₁ k₂ a_v
  exact ⟨SplitOctonionIsotropicAmariStage.causalEdge_acyclic,
    ParaKahlerSuperGrassmannianAmariStage.causalEdge_acyclic,
    ParaKahlerSuperGrassmannianAmariStage.fromSplitOctonionStage_monotone,
    rfl,
    hO.2.2.1.1,
    hO.2.2.2.2.1,
    hO.2.2.2.2.2.1,
    hO.2.2.2.2.2.2,
    hP12.2.2.2.2.2.2.2.2.2.1,
    hP12.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hP3.2.2.2.2.2.2.2.1,
    hP3.2.2.2.2.2.2.2.2.2.2.2.1,
    hP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hP4.2.2.2.2.1,
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hP5.2.1,
    hP5.2.2.2.2.1,
    hP6.1,
    hP6.2.2.2.1,
    hP6.2.2.2.2.2.1,
    hP6.2.2.2.2.2.2.2⟩

end InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBerezinianAmariPoset
