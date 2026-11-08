/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
import InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
import InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
import InfoGeometry.Canonical.OperatorBerezinianCore
import InfoGeometry.Canonical.OperatorLogDetDikinGeometry
import InfoGeometry.Supergeometry.BerezinianDecomposition
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# The 7-Stage Para-Kähler Super-Grassmannian, Bruhat-Dressed Two-Chart Idempotent, Push–Pull Intertwiner & Hua–Bergman–Dikin Metric Poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`)

===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset
Role: Canonical native Mathlib formalization of the **Para-Kähler Super-Grassmannian
  (`Gr(m|n, p|q)`), Unipotent Single-Chart Flatness vs. Two-Chart Para-Kähler
  Curvature, Exact Bruhat-Dressed Two-Chart Idempotent (`P̂ = (1 - N_+)(P + N_-)(1 + N_+)
  = P + Φ - Σ - V N_+`, `P̂² = P̂`), Associative Push–Pull Intertwining Law
  (`Q_+^n N_+ = N_+ Q_-^n = V^n N_+` and `(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹`),
  Legendre–Schur Differential & Hua–Bergman–Dikin Para-Kähler Metric
  (`dη_- = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹`), Super-LU Bergman Berezinian
  Factorization (`(1 - Q_+)(1 - Q_-) = 1 - V`), and Unified Split-Octonion →
  Super-Grassmannian → Para-Kähler Amari Closure** (`𝔓₁ ≺ 𝔓₂ ≺ … ≺ 𝔓₇`),
  reusing and bridging:
  * `InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized` (`conePlus`,
    `coneMinus`, `genPhi`, `genJ`, `genV`, `genSig`, `invS`, `peirce_nf`),
  * `InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset`
    (`amariExpPlus`, `amariExpMinus`, `qgtPlus`, `qgtMinus`,
    `AmariDuallyFlatOperatorStage`, `FirstQuantizedAmariStage`),
  * `InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset`
    (`SplitOctonionIsotropicAmariStage`, `stage_O3_O4_O5_noncommutative_dewitt_sum_metric_and_difference_curvature`),
  * `InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset`
    (`peirceLeftElimShear`, `peirceRightElimShear`, `peirceSchurComplement`,
    `peirceSchurComplement_unipotent_block_diagonalization`),
  * `InfoGeometry.Supergeometry.Berezinian` (`berezinian`, `factorL`, `factorH`,
    `factorR`, `super_lu_factorization`),
  * `InfoGeometry.Canonical.OperatorLogDetDikinGeometry` (`hessianMap_negLogDet`).

Main Mathematical Results (Zero `sorry`, Zero `admit`, Zero Custom Axioms):
1. **7-Stage Acyclic Causal Poset (`ParaKahlerSuperGrassmannianStage`: `𝔓₁ ≺ … ≺ 𝔓₇`)**:
   - `ParaKahlerSuperGrassmannianStage.causalEdge_acyclic`: strict acyclicity of
     `𝔓₁ ≺ 𝔓₂ ≺ 𝔓₃ ≺ 𝔓₄ ≺ 𝔓₅ ≺ 𝔓₆ ≺ 𝔓₇`,
   - Order-preserving isomorphisms onto `SplitOctonionIsotropicAmariStage` (`𝔒₁ ≺ … ≺ 𝔒₇`)
     and `AmariDuallyFlatOperatorStage` (`𝔇₁ ≺ … ≺ 𝔇₇`).
2. **Rung 0 & Stages `𝔓₁, 𝔓₂` (`rung0_and_stage_P1_P2_unipotent_charts_vs_linear_superposition_aporia`)**:
   - In any noncommutative `[Ring B]` with idempotent `P * P = P`, the Chiral DeWitt
     Difference Involution `S_P = 2P - 1` (`S_P² = 1`) splits the tangent space into
     the `+1` left-eigenbundle `𝔫_+` (`S_P * N_+ = N_+`) and `-1` left-eigenbundle
     `𝔫_-` (`S_P * N_- = -N_-`).
   - Single-chart unipotent dressings `P_+(A) = (1 - N_+(A)) * P * (1 + N_+(A)) = P + N_+(A)`
     and `P_-(C) = (1 + N_-(C)) * P * (1 - N_-(C)) = P + N_-(C)` are exact idempotents
     (`P_+² = P_+`, `P_-² = P_-`) with Abelian chart translations, whereas the naive
     linear superposition `Ψ = P + N_+ + N_- = P + Φ` jumps off the Super-Grassmannian
     with quadratic defect `Ψ² - Ψ = V(A, C)` (`Ψ² = Ψ ↔ V(A, C) = 0`), and the two-chart
     commutator exposes the Para-Kähler curvature `[P_+(A), P_-(C)] = Σ(A, C) - Φ(A, C)`.
3. **Stage `𝔓₃` (`stage_P3_bruhat_dressed_two_chart_idempotent_cancels_aporia`)**:
   - Dressing the dual chart `P + N_-(C)` by the primal unipotent exponential `1 ± N_+(A)`
     produces the **Bruhat-Dressed Two-Chart Projector**:
     `P̂(P, A, C) := (1 - N_+(A)) * (P + N_-(C)) * (1 + N_+(A))
                  = P + Φ(A, C) - Σ(A, C) - V(A, C) * N_+(A)
                  = P + Φ(A, C) - Σ(A, C) - N_+(A) * N_-(C) * N_+(A)`,
     which is an **exact idempotent** (`P̂² = P̂`) across the entire curved manifold!
   - The dual Bruhat dressing `P̂_dual(P, A, C) := (1 + N_-(C)) * (P + N_+(A)) * (1 - N_-(C))
     = P + Φ(A, C) - Σ(A, C) - V(A, C) * N_-(C)` is likewise an exact idempotent, and
     their difference is purely cubic along the timelike current `J = N_+ - N_-`:
     `P̂_dual(P, A, C) - P̂(P, A, C) = V(A, C) * J(A, C)`.
4. **Stage `𝔓₄` (`stage_P4_push_pull_intertwiner_and_resolvent_equivariance`)**:
   - Proves the universal associative Push–Pull Intertwining Law across the chiral sheets:
     `Q_+ * N_+ = N_+ * Q_- = V * N_+ = N_+ * V = N_+ * N_- * N_+`,
     `Q_+^n * N_+ = N_+ * Q_-^n = V^n * N_+ = N_+ * V^n` for all `n : ℕ`,
     `(1 - Q_+) * N_+ = N_+ * (1 - Q_-) = (1 - V) * N_+ = N_+ * (1 - V)`, and for any
     units `U_+, U_-, U_V : Bˣ` representing `1 - Q_+, 1 - Q_-, 1 - V`:
     `(↑U_+⁻¹ : B) * N_+ = N_+ * (↑U_-⁻¹ : B) = (↑U_V⁻¹ : B) * N_+ = N_+ * (↑U_V⁻¹ : B)`.
5. **Stage `𝔓₅` (`stage_P5_legendre_schur_differential_and_hua_bergman_dikin_metric`)**:
   - Proves that the two-term Leibniz differential of the Legendre–Schur expectation
     coordinate `η_- = (1 - Q_+)⁻¹ N_+` along `dN_+ = N_+(P, dA)` collapses via the
     Push–Pull Intertwiner into a single factored product:
     `dη_- = (1 - Q_+)⁻¹ dN_+ + (1 - Q_+)⁻¹ dN_+ N_- (1 - Q_+)⁻¹ N_+
           = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ dN_+ (1 - V)⁻¹`,
     so pairing with `dN_- = N_-(P, dC)` yields the exact **Hua–Bergman–Dikin Para-Kähler
     Operator Metric** `G_V(dN_+, dN_-) = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹ dN_- = (1 - V)⁻¹ dN_+ (1 - V)⁻¹ dN_-`
     and bridges it to `OperatorLogDetDikinGeometry.hessianMap_negLogDet`.
6. **Stage `𝔓₆` (`stage_P6_super_lu_bergman_berezinian_and_split_factorization`)**:
   - Proves that unipotent Peirce–Gauss elimination block-diagonalizes `1 + N_+ + N_-`
     into `1 - Q_+` in the primal order and `1 - Q_-` in the dual order, that the upper
     and lower Bergman kernels commute and multiply to `1 - V`:
     `(1 - Q_+) * (1 - Q_-) = 1 - V = (1 - Q_-) * (1 - Q_+)`,
     and bridges to the `2 × 2` Super-LU Berezinian (`InfoGeometry.Supergeometry.Berezinian.super_lu_factorization`)
     and the chiral-weighted truncated log-Berezinian potential `S_P * 𝓚_2(V) = Σ + ½ S_P V²`.
7. **Stage `𝔓₇` (`para_kahler_super_grassmannian_bruhat_push_pull_dikin_master_poset`)**:
   - Unifies `𝔓₁ ≺ … ≺ 𝔓₇` with the Split-Octonion Isotropic Poset (`𝔒₁ ≺ … ≺ 𝔒₇`)
     and First-Quantized Amari Operator Geometry (`𝔇₁ ≺ … ≺ 𝔇₇`, `𝔔₁ ≺ … ≺ 𝔔₆`).

### Three-Bucket Audit Map

#### BUCKET 1 — Unconditional Kernel Truth
- `ParaKahlerSuperGrassmannianStage`, `rank_injective`, `card_eq_seven`, `causalEdge_strictMono`,
  `causalEdge_transGen_strictMono`, `causalEdge_acyclic`.

#### BUCKET 2 — Conditional Kernel Theorems with Explicit Hypotheses
- Stages `𝔓₁`–`𝔓₇` Bruhat-dressed two-chart idempotent, push–pull resolvent equivariance,
  Legendre–Schur differential collapse, and Super-LU Bergman Berezinian theorems under explicit
  idempotent and unit-resolvent hypotheses.

#### BUCKET 3 — Open / Beyond-Scope Obligations
- Infinite-dimensional Fredholm determinant Berezinians on Hilbert–Schmidt super-Grassmannians
  remain outside this algebraic and finite-matrix scope.

## i. Overview
Formalizes the 7-stage Para-Kähler Super-Grassmannian, Bruhat-dressed two-chart idempotent, push–pull resolvent intertwiner, and Hua–Bergman–Dikin metric poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`).

## ii. Key results
- `ParaKahlerSuperGrassmannianStage.causalEdge_acyclic`
- `ParaKahlerSuperGrassmannianStage.card_eq_seven`

## iii. Table of contents
- Section 1: The 7-Stage Para-Kähler Super-Grassmannian Causal Poset (`𝔓₁ ≺ ⋯ ≺ 𝔓₇`)
- Sections 2–7: Stages `𝔓₁`–`𝔓₇`

## iv. References
- L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains* (1963).
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset (Vec3 ZornMatrix)
open InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
open InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
open InfoGeometry.Canonical.SupergradedMoebiusTetraktysKleinQuotientBerezinianWeylPoset
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Geometry.LegendreDifferential
open InfoGeometry.Canonical.OperatorLogDetDikinGeometry
open InfoGeometry.Supergeometry.Berezinian

/-! ===========================================================================
    Section 1: The 7-Stage Para-Kähler Super-Grassmannian Causal Poset (`𝔓₁ ≺ … ≺ 𝔓₇`)
    =========================================================================== -/

/-- The 7 causal stages of the **Para-Kähler Super-Grassmannian, Bruhat-Dressed
Two-Chart Idempotent, Push–Pull Resolvent Intertwiner & Hua–Bergman–Dikin Metric
Poset** (`𝔓₁ ≺ 𝔓₂ ≺ 𝔓₃ ≺ 𝔓₄ ≺ 𝔓₅ ≺ 𝔓₆ ≺ 𝔓₇`). -/
inductive ParaKahlerSuperGrassmannianStage : Type
  /-- `𝔓₁`: Para-Kähler tangent polarization of the Super-Grassmannian (`P² = P`,
      `S_P = 2P - 1`, `S_P² = 1`, `T_P Gr = 𝔫_+ ⊕ 𝔫_-`, `S_P|_{𝔫_±} = ±id`). -/
  | P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit
  /-- `𝔓₂`: Single-chart unipotent idempotency (`P_+(N_+)² = P_+(N_+)`,
      `P_-(N_-)² = P_-(N_-)`) vs. two-chart Para-Kähler commutator curvature
      (`[P_+, P_-] = Σ - Φ`). -/
  | P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature
  /-- `𝔓₃`: Exact Bruhat-dressed two-chart idempotent
      (`P̂ = (1 - N_+)(P + N_-)(1 + N_+) = P + Φ - Σ - V N_+`, `P̂² = P̂`)
      canceling the Socratic aporia via the Jordan triple product `-V N_+`. -/
  | P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation
  /-- `𝔓₄`: Associative Push–Pull intertwining law across the chiral sheets
      (`Q_+^n N_+ = N_+ Q_-^n = V^n N_+` and `(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ N_+`). -/
  | P4_AssociativePushPullIntertwinerAndResolventEquivariance
  /-- `𝔓₅`: Legendre–Schur differential collapse (`dη_- = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹`)
      and the Hua–Bergman–Dikin Para-Kähler operator metric
      (`G_V(dN_+, dN_-) = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹ dN_-`). -/
  | P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
  /-- `𝔓₆`: Super-LU Bergman Berezinian factorization (`(1 - Q_+)(1 - Q_-) = 1 - V`),
      `2 × 2` Super-LU Berezinian, and chiral-weighted truncated log-Berezinian potential. -/
  | P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential
  /-- `𝔓₇`: Unified Split-Octonion (`𝕆_s`) → Super-Grassmannian (`Gr(m|n, p|q)`) →
      Para-Kähler Amari Operator Geometry closure. -/
  | P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure
  deriving DecidableEq, Repr, Inhabited

namespace ParaKahlerSuperGrassmannianStage

/-- Numerical rank `0..6` of the 7 stages `𝔓₁..𝔓₇`. -/
def rank : ParaKahlerSuperGrassmannianStage → ℕ
  | .P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit => 0
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature => 1
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation => 2
  | .P4_AssociativePushPullIntertwinerAndResolventEquivariance => 3
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric => 4
  | .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential => 5
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure => 6

/-- The stage rank map `rank` is injective on `ParaKahlerSuperGrassmannianStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder ParaKahlerSuperGrassmannianStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype ParaKahlerSuperGrassmannianStage where
  elems := {
    .P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit,
    .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature,
    .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation,
    .P4_AssociativePushPullIntertwinerAndResolventEquivariance,
    .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric,
    .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential,
    .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure
  }
  complete x := by cases x <;> simp

/-- The 7-stage `ParaKahlerSuperGrassmannianStage` poset has exact cardinality `7`. -/
theorem card_eq_seven : Fintype.card ParaKahlerSuperGrassmannianStage = 7 := by
  decide

/-- Directed causal edges of the poset `𝔓₁ ≺ 𝔓₂ ≺ 𝔓₃ ≺ 𝔓₄ ≺ (𝔓₅, 𝔓₆) ≺ 𝔓₇`. -/
inductive causalEdge : ParaKahlerSuperGrassmannianStage → ParaKahlerSuperGrassmannianStage → Prop
  | p1_to_p2 : causalEdge .P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit
      .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature
  | p2_to_p3 : causalEdge .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature
      .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation
  | p3_to_p4 : causalEdge .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation
      .P4_AssociativePushPullIntertwinerAndResolventEquivariance
  | p4_to_p5 : causalEdge .P4_AssociativePushPullIntertwinerAndResolventEquivariance
      .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
  | p4_to_p6 : causalEdge .P4_AssociativePushPullIntertwinerAndResolventEquivariance
      .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential
  | p5_to_p6 : causalEdge .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
      .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential
  | p5_to_p7 : causalEdge .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric
      .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure
  | p6_to_p7 : causalEdge .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential
      .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure

/-- Every directed causal edge strictly increases the stage order. -/
theorem causalEdge_strictMono {a b : ParaKahlerSuperGrassmannianStage}
    (h : causalEdge a b) : a < b := by
  cases h <;> decide

/-- Any transitive path of causal edges strictly increases the stage order. -/
theorem causalEdge_transGen_strictMono {a b : ParaKahlerSuperGrassmannianStage}
    (h : Relation.TransGen causalEdge a b) : a < b := by
  induction h with
  | single hstep => exact causalEdge_strictMono hstep
  | tail _ hstep ih => exact lt_trans ih (causalEdge_strictMono hstep)

-- theorem-class: structural Setup/bridge
/-- The 7-stage Para-Kähler Super-Grassmannian poset `𝔓₁ ≺ … ≺ 𝔓₇` is strictly acyclic. -/
theorem causalEdge_acyclic (s : ParaKahlerSuperGrassmannianStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (causalEdge_transGen_strictMono h)

/-- Order-preserving bijection onto `SplitOctonionIsotropicAmariStage` (`𝔒₁ ≺ … ≺ 𝔒₇`). -/
def toSplitOctonionStage : ParaKahlerSuperGrassmannianStage → SplitOctonionIsotropicAmariStage
  | .P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit =>
      .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature =>
      .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation =>
      .O3_BiLagrangianMetricSplitAndCrossVacuumProjection
  | .P4_AssociativePushPullIntertwinerAndResolventEquivariance =>
      .O4_DeWittSumOperatorFisherMetric
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric =>
      .O5_DeWittDifferenceBerrySkewnessCurvature
  | .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential =>
      .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure =>
      .O7_NonCommutativeNambuAssociatorOnDeWittDifference

-- theorem-class: structural Setup/bridge
/-- `toSplitOctonionStage` is strictly monotone (`𝔓ᵢ < 𝔓ⱼ ↔ 𝔒ᵢ < 𝔒ⱼ`). -/
theorem toSplitOctonionStage_strictMono : StrictMono toSplitOctonionStage := by
  intro a b hab
  change rank a < rank b at hab
  change (toSplitOctonionStage a).stageIndex < (toSplitOctonionStage b).stageIndex
  cases a <;> cases b <;> revert hab <;> decide

/-- Order-preserving bijection onto `AmariDuallyFlatOperatorStage` (`𝔇₁ ≺ … ≺ 𝔇₇`). -/
def toAmariStage : ParaKahlerSuperGrassmannianStage → AmariDuallyFlatOperatorStage
  | .P1_ParaKahlerTangentPolarizationAndChiralDeWittSplit =>
      .D1_ChiralSplitIntoDuallyFlatAffineSubalgebras
  | .P2_SingleChartUnipotentIdempotencyAndTwoChartCommutatorCurvature =>
      .D2_ExactAbelianExponentialFamilies
  | .P3_BruhatDressedTwoChartIdempotentAndJordanTripleCancellation =>
      .D3_PairedOperatorGaussiansAndExactInversion
  | .P4_AssociativePushPullIntertwinerAndResolventEquivariance =>
      .D4_BirthOfFisherMetricAndBerrySkewnessFromCrossCollision
  | .P5_LegendreSchurDifferentialAndHuaBergmanDikinParaKahlerMetric =>
      .D5_AmariDualConnectionsMidpointAndSkewnessSplit
  | .P6_SuperLUBergmanBerezinianAndBigradedV4SuperPotential =>
      .D6_OperatorPythagoreanTheoremAndOrthogonalGramians
  | .P7_UnifiedSplitOctonionSuperGrassmannianParaKahlerAmariClosure =>
      .D7_LegendreResolventDualityBregmanAndBKMClosure

-- theorem-class: structural Setup/bridge
/-- `toAmariStage` is strictly monotone (`𝔓ᵢ < 𝔓ⱼ ↔ 𝔇ᵢ < 𝔇ⱼ`). -/
theorem toAmariStage_strictMono : StrictMono toAmariStage := by
  intro a b hab
  change rank a < rank b at hab
  change (toAmariStage a).stageIndex < (toAmariStage b).stageIndex
  cases a <;> cases b <;> revert hab <;> decide

end ParaKahlerSuperGrassmannianStage

/-! ===========================================================================
    Section 2: Concrete `2 × 2` Integer Matrix Non-Commutativity & Dressed
    Idempotent Witnesses
    =========================================================================== -/

/-- Base idempotent `P_mat = E₀₀ = !![1, 0; 0, 0]` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def superGrassmannWitnessP : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 0]

/-- Primal unipotent Super-Grassmannian chart `P_+(1) = !![1, 1; 0, 0]`. -/
def superGrassmannWitnessChartPlus : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 0, 0]

/-- Dual unipotent Super-Grassmannian chart `P_-(1) = !![1, 0; 1, 0]`. -/
def superGrassmannWitnessChartMinus : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 1, 0]

/-- Naive linear superposition `Ψ_mat = P_mat + E₀₁ + E₁₀ = !![1, 1; 1, 0]`. -/
def superGrassmannWitnessNaiveSum : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 0]

/-- Bruhat-dressed two-chart projector
`P̂_mat = (I - E₀₁)(P_mat + E₁₀)(I + E₀₁) = !![0, 0; 1, 1]`. -/
def superGrassmannWitnessDressed : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0; 1, 1]

-- theorem-class: constructive endpoint
/-- Concrete `2 × 2` integer matrix witness demonstrating:
1. `superGrassmannWitnessChartPlus` and `superGrassmannWitnessChartMinus` are
   individually idempotent (`P_+² = P_+`, `P_-² = P_-`),
2. They do NOT commute (`P_+ * P_- ≠ P_- * P_+`),
3. Their naive linear superposition `superGrassmannWitnessNaiveSum` is NOT idempotent
   (`Ψ² ≠ Ψ`),
4. The Bruhat-dressed two-chart projector `superGrassmannWitnessDressed` IS an exact
   idempotent (`P̂² = P̂`). -/
theorem superGrassmannWitness_noncomm_aporia_and_dressed_idempotent :
    superGrassmannWitnessChartPlus * superGrassmannWitnessChartPlus =
      superGrassmannWitnessChartPlus ∧
    superGrassmannWitnessChartMinus * superGrassmannWitnessChartMinus =
      superGrassmannWitnessChartMinus ∧
    superGrassmannWitnessChartPlus * superGrassmannWitnessChartMinus ≠
      superGrassmannWitnessChartMinus * superGrassmannWitnessChartPlus ∧
    superGrassmannWitnessNaiveSum * superGrassmannWitnessNaiveSum ≠
      superGrassmannWitnessNaiveSum ∧
    superGrassmannWitnessDressed * superGrassmannWitnessDressed =
      superGrassmannWitnessDressed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    revert h01
    decide
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    revert h00
    decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide

/-! ===========================================================================
    Section 3: Rung 0 & Stages `𝔓₁, 𝔓₂` — Para-Kähler Tangent Polarization,
    Unipotent Single-Chart Idempotency (`P_±² = P_±`), Naive Linear Superposition
    Aporia (`Ψ² - Ψ = V`), & Two-Chart Commutator Curvature (`[P_+, P_-] = Σ - Φ`)
    =========================================================================== -/

section StagesP1P2UnipotentChartsAndLinearSuperpositionAporia

variable {B : Type*} [Ring B]

/-- The Primal `e`-Isotropic Super-Grassmannian Chart Projector
`superGrassmannPrimalChart P A := P + N_+(P, A)`. -/
def superGrassmannPrimalChart (P A : B) : B :=
  P + conePlus P A

/-- The Dual `m`-Isotropic Super-Grassmannian Chart Projector
`superGrassmannDualChart P C := P + N_-(P, C)`. -/
def superGrassmannDualChart (P C : B) : B :=
  P + coneMinus P C

/-- The Naive Linear Superposition of the Primal and Dual Charts
`superGrassmannNaiveSum P A C := P + N_+(P, A) + N_-(P, C) = P + Φ(P, A, C)`. -/
def superGrassmannNaiveSum (P A C : B) : B :=
  P + conePlus P A + coneMinus P C

-- theorem-class: constructive endpoint
/-- **Rung 0 & Stages `𝔓₁, 𝔓₂` Theorem
(`rung0_and_stage_P1_P2_unipotent_charts_vs_linear_superposition_aporia`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Stage `𝔓₁` (Para-Kähler Tangent Polarization by `S_P = 2P - 1`)**:
   * `invS P * invS P = 1`,
   * `invS P * conePlus P A = conePlus P A` and
     `conePlus P A * invS P = -conePlus P A` (`+1` chiral eigenbundle `T_P^(1,0) = 𝔫_+`),
   * `invS P * coneMinus P C = -coneMinus P C` and
     `coneMinus P C * invS P = coneMinus P C` (`-1` chiral eigenbundle `T_P^(0,1) = 𝔫_-`).
2. **Stage `𝔓₂` (Unipotent Single-Chart Dressings, Exact Idempotency & Abelian Shifts)**:
   * `amariExpPlus P (-A) * P * amariExpPlus P A = superGrassmannPrimalChart P A`,
   * `amariExpMinus P C * P * amariExpMinus P (-C) = superGrassmannDualChart P C`,
   * `superGrassmannPrimalChart P A * superGrassmannPrimalChart P A = superGrassmannPrimalChart P A`,
   * `superGrassmannDualChart P C * superGrassmannDualChart P C = superGrassmannDualChart P C`,
   * `amariExpPlus P (-B₀) * superGrassmannPrimalChart P A * amariExpPlus P B₀ =
        superGrassmannPrimalChart P (A + B₀)`,
   * `amariExpMinus P D₀ * superGrassmannDualChart P C * amariExpMinus P (-D₀) =
        superGrassmannDualChart P (C + D₀)`.
3. **Rung 0 Socratic Aporia (Linear Superposition Jumps Off the Super-Grassmannian)**:
   * `superGrassmannNaiveSum P A C = P + genPhi P A C`,
   * `superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C -
        superGrassmannNaiveSum P A C = genV P A C`,
   * `superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C =
        superGrassmannNaiveSum P A C ↔ genV P A C = 0`.
4. **Two-Chart Products & Para-Kähler Symplectic Commutator Curvature**:
   * `superGrassmannPrimalChart P A * superGrassmannDualChart P C =
        P + qgtPlus P A C`,
   * `superGrassmannDualChart P C * superGrassmannPrimalChart P A =
        P + genPhi P A C + qgtMinus P A C`,
   * `superGrassmannPrimalChart P A * superGrassmannDualChart P C -
        superGrassmannDualChart P C * superGrassmannPrimalChart P A =
          genSig P A C - genPhi P A C`. -/
theorem rung0_and_stage_P1_P2_unipotent_charts_vs_linear_superposition_aporia
    {P : B} (hP : P * P = P) (A B₀ C D₀ : B) :
    -- (1) Stage 𝔓₁: Para-Kähler polarization by S_P = 2P - 1
    (invS P * invS P = 1 ∧
      invS P * conePlus P A = conePlus P A ∧
      conePlus P A * invS P = -conePlus P A ∧
      invS P * coneMinus P C = -coneMinus P C ∧
      coneMinus P C * invS P = coneMinus P C) ∧
    -- (2) Stage 𝔓₂: Unipotent single-chart dressings, idempotency & Abelian shifts
    (amariExpPlus P (-A) * P * amariExpPlus P A = superGrassmannPrimalChart P A ∧
      amariExpMinus P C * P * amariExpMinus P (-C) = superGrassmannDualChart P C ∧
      superGrassmannPrimalChart P A * superGrassmannPrimalChart P A =
        superGrassmannPrimalChart P A ∧
      superGrassmannDualChart P C * superGrassmannDualChart P C =
        superGrassmannDualChart P C ∧
      amariExpPlus P (-B₀) * superGrassmannPrimalChart P A * amariExpPlus P B₀ =
        superGrassmannPrimalChart P (A + B₀) ∧
      amariExpMinus P D₀ * superGrassmannDualChart P C * amariExpMinus P (-D₀) =
        superGrassmannDualChart P (C + D₀)) ∧
    -- (3) Rung 0 Socratic Aporia: Naive linear superposition jumps off the manifold
    (superGrassmannNaiveSum P A C = P + genPhi P A C ∧
      superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C -
        superGrassmannNaiveSum P A C = genV P A C ∧
      (superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C =
        superGrassmannNaiveSum P A C ↔ genV P A C = 0)) ∧
    -- (4) Two-chart products & Para-Kähler commutator curvature
    (superGrassmannPrimalChart P A * superGrassmannDualChart P C =
        P + qgtPlus P A C ∧
      superGrassmannDualChart P C * superGrassmannPrimalChart P A =
        P + genPhi P A C + qgtMinus P A C ∧
      superGrassmannPrimalChart P A * superGrassmannDualChart P C -
        superGrassmannDualChart P C * superGrassmannPrimalChart P A =
          genSig P A C - genPhi P A C) := by
  have hDefect :
      superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C -
        superGrassmannNaiveSum P A C = genV P A C := by
    dsimp [superGrassmannNaiveSum]
    peirce_nf hP
  refine ⟨⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
           by peirce_nf hP, by peirce_nf hP⟩,
    ⟨by dsimp [amariExpPlus, superGrassmannPrimalChart]; peirce_nf hP,
     by dsimp [amariExpMinus, superGrassmannDualChart]; peirce_nf hP,
     by dsimp [superGrassmannPrimalChart]; peirce_nf hP,
     by dsimp [superGrassmannDualChart]; peirce_nf hP,
     by dsimp [amariExpPlus, superGrassmannPrimalChart]; peirce_nf hP,
     by dsimp [amariExpMinus, superGrassmannDualChart]; peirce_nf hP⟩,
    ⟨by dsimp [superGrassmannNaiveSum]; peirce_nf hP,
     hDefect,
     ⟨fun hId => by rw [← hDefect, hId, sub_self],
      fun hV0 => sub_eq_zero.mp (hDefect.trans hV0)⟩⟩,
    ⟨by dsimp [superGrassmannPrimalChart, superGrassmannDualChart,
          qgtPlus]; peirce_nf hP,
     by dsimp [superGrassmannPrimalChart, superGrassmannDualChart,
          qgtMinus]; peirce_nf hP,
     by dsimp [superGrassmannPrimalChart, superGrassmannDualChart]; peirce_nf hP⟩⟩

end StagesP1P2UnipotentChartsAndLinearSuperpositionAporia

/-! ===========================================================================
    Section 4: Stage `𝔓₃` — Exact Bruhat-Dressed Two-Chart Idempotent
    (`P̂ = (1 - N_+)(P + N_-)(1 + N_+) = P + Φ - Σ - V N_+`, `P̂² = P̂`)
    =========================================================================== -/

section StageP3BruhatDressedTwoChartIdempotent

variable {B : Type*} [Ring B]

/-- The **Primal Bruhat-Dressed Two-Chart Super-Grassmannian Projector**
`bruhatDressedProjector P A C := (1 - N_+(P, A)) * (P + N_-(P, C)) * (1 + N_+(P, A))`. -/
def bruhatDressedProjector (P A C : B) : B :=
  amariExpPlus P (-A) * superGrassmannDualChart P C * amariExpPlus P A

/-- The **Dual Bruhat-Dressed Two-Chart Super-Grassmannian Projector**
`bruhatDressedDualProjector P A C := (1 + N_-(P, C)) * (P + N_+(P, A)) * (1 - N_-(P, C))`. -/
def bruhatDressedDualProjector (P A C : B) : B :=
  amariExpMinus P C * superGrassmannPrimalChart P A * amariExpMinus P (-C)

/-- The **Primal Jordan Triple Product** `peirceJordanTriplePlus P A C := N_+(P, A) * N_-(P, C) * N_+(P, A)`. -/
def peirceJordanTriplePlus (P A C : B) : B :=
  conePlus P A * coneMinus P C * conePlus P A

/-- The **Dual Jordan Triple Product** `peirceJordanTripleMinus P A C := N_-(P, C) * N_+(P, A) * N_-(P, C)`. -/
def peirceJordanTripleMinus (P A C : B) : B :=
  coneMinus P C * conePlus P A * coneMinus P C

-- theorem-class: constructive endpoint
/-- **Stage `𝔓₃` Theorem (`stage_P3_bruhat_dressed_two_chart_idempotent_cancels_aporia`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Jordan Triple Products Equal `V * N_±`**:
   * `peirceJordanTriplePlus P A C = genV P A C * conePlus P A`,
   * `peirceJordanTriplePlus P A C = qgtPlus P A C * conePlus P A`,
   * `peirceJordanTripleMinus P A C = genV P A C * coneMinus P C`,
   * `peirceJordanTripleMinus P A C = qgtMinus P A C * coneMinus P C`.
2. **Explicit Expansion of the Primal Bruhat-Dressed Two-Chart Projector `P̂`**:
   * `bruhatDressedProjector P A C =
        P + genPhi P A C - genSig P A C -
          genV P A C * conePlus P A`,
   * `bruhatDressedProjector P A C =
        superGrassmannNaiveSum P A C - genSig P A C -
          peirceJordanTriplePlus P A C`.
3. **Exact Idempotency on the Curved Manifold (`P̂² = P̂` & `P̂_dual² = P̂_dual`)**:
   * `bruhatDressedProjector P A C * bruhatDressedProjector P A C =
        bruhatDressedProjector P A C`,
   * `bruhatDressedDualProjector P A C =
        P + genPhi P A C - genSig P A C -
          genV P A C * coneMinus P C`,
   * `bruhatDressedDualProjector P A C * bruhatDressedDualProjector P A C =
        bruhatDressedDualProjector P A C`.
4. **Difference Between Primal and Dual Dressings Is Purely Cubic Along `J = N_+ - N_-`**:
   * `bruhatDressedDualProjector P A C - bruhatDressedProjector P A C =
        genV P A C * genJ P A C`. -/
theorem stage_P3_bruhat_dressed_two_chart_idempotent_cancels_aporia
    {P : B} (hP : P * P = P) (A C : B) :
    -- (1) Jordan triple products equal V * N_±
    (peirceJordanTriplePlus P A C = genV P A C * conePlus P A ∧
      peirceJordanTriplePlus P A C = qgtPlus P A C * conePlus P A ∧
      peirceJordanTripleMinus P A C = genV P A C * coneMinus P C ∧
      peirceJordanTripleMinus P A C = qgtMinus P A C * coneMinus P C) ∧
    -- (2) Explicit expansion of P̂ into linear tangent Φ, curvature -Σ, and Jordan triple -V N_+
    (bruhatDressedProjector P A C =
        P + genPhi P A C - genSig P A C -
          genV P A C * conePlus P A ∧
      bruhatDressedProjector P A C =
        superGrassmannNaiveSum P A C - genSig P A C -
          peirceJordanTriplePlus P A C) ∧
    -- (3) Exact idempotency P̂² = P̂ and P̂_dual² = P̂_dual
    (bruhatDressedProjector P A C * bruhatDressedProjector P A C =
        bruhatDressedProjector P A C ∧
      bruhatDressedDualProjector P A C =
        P + genPhi P A C - genSig P A C -
          genV P A C * coneMinus P C ∧
      bruhatDressedDualProjector P A C * bruhatDressedDualProjector P A C =
        bruhatDressedDualProjector P A C) ∧
    -- (4) Primal-dual dressing difference is V * J
    (bruhatDressedDualProjector P A C - bruhatDressedProjector P A C =
      genV P A C * genJ P A C) := by
  refine ⟨⟨by dsimp [peirceJordanTriplePlus]; peirce_nf hP,
           rfl,
           by dsimp [peirceJordanTripleMinus]; peirce_nf hP,
           rfl⟩,
    ⟨by dsimp [bruhatDressedProjector, amariExpPlus, superGrassmannDualChart]; peirce_nf hP,
     by dsimp [bruhatDressedProjector, amariExpPlus, superGrassmannDualChart,
          superGrassmannNaiveSum, peirceJordanTriplePlus]; peirce_nf hP⟩,
    ⟨by dsimp [bruhatDressedProjector, amariExpPlus, superGrassmannDualChart]; peirce_nf hP,
     by dsimp [bruhatDressedDualProjector, amariExpMinus, superGrassmannPrimalChart]; peirce_nf hP,
     by dsimp [bruhatDressedDualProjector, amariExpMinus, superGrassmannPrimalChart]; peirce_nf hP⟩,
    by dsimp [bruhatDressedDualProjector, bruhatDressedProjector,
         amariExpPlus, amariExpMinus, superGrassmannPrimalChart,
         superGrassmannDualChart]; peirce_nf hP⟩

end StageP3BruhatDressedTwoChartIdempotent

/-! ===========================================================================
    Section 5: Stage `𝔓₄` — Associative Push–Pull Intertwining Law Across the
    Chiral Sheets (`Q_+^n N_+ = N_+ Q_-^n = V^n N_+` &
    `(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ N_+`)
    =========================================================================== -/

section StageP4PushPullIntertwinerAndResolventEquivariance

variable {B : Type*} [Ring B]

-- theorem-class: domain-helper
/-- Single-step Push–Pull Intertwining Identities between `Q_+ = N_+ N_-`,
`Q_- = N_- N_+`, `V = Q_+ + Q_-`, and `N_+, N_-`. -/
theorem peirce_push_pull_one {P : B} (hP : P * P = P) (A C : B) :
    (qgtPlus P A C * conePlus P A =
        conePlus P A * qgtMinus P A C ∧
      genV P A C * conePlus P A =
        qgtPlus P A C * conePlus P A ∧
      conePlus P A * genV P A C =
        conePlus P A * qgtMinus P A C ∧
      qgtMinus P A C * conePlus P A = 0 ∧
      conePlus P A * qgtPlus P A C = 0) ∧
    (qgtMinus P A C * coneMinus P C =
        coneMinus P C * qgtPlus P A C ∧
      genV P A C * coneMinus P C =
        qgtMinus P A C * coneMinus P C ∧
      coneMinus P C * genV P A C =
        coneMinus P C * qgtPlus P A C ∧
      qgtPlus P A C * coneMinus P C = 0 ∧
      coneMinus P C * qgtMinus P A C = 0) := by
  refine ⟨⟨by dsimp [qgtPlus, qgtMinus]; peirce_nf hP,
           by dsimp [qgtPlus]; peirce_nf hP,
           by dsimp [qgtMinus]; peirce_nf hP,
           by dsimp [qgtMinus]; peirce_nf hP,
           by dsimp [qgtPlus]; peirce_nf hP⟩,
    ⟨by dsimp [qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [qgtMinus]; peirce_nf hP,
     by dsimp [qgtPlus]; peirce_nf hP,
     by dsimp [qgtPlus]; peirce_nf hP,
     by dsimp [qgtMinus]; peirce_nf hP⟩⟩

-- theorem-class: constructive endpoint
/-- **All-Power Push–Pull Intertwining Induction (`peirce_push_pull_pow`)**:
For every natural number `n : ℕ` (including `n = 0`):
1. `Q_+^n * N_+ = N_+ * Q_-^n`, `V^n * N_+ = Q_+^n * N_+`, and `N_+ * V^n = N_+ * Q_-^n`,
2. `Q_-^n * N_- = N_- * Q_+^n`, `V^n * N_- = Q_-^n * N_-`, and `N_- * V^n = N_- * Q_+^n`. -/
theorem peirce_push_pull_pow {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    (qgtPlus P A C ^ n * conePlus P A =
        conePlus P A * qgtMinus P A C ^ n ∧
      genV P A C ^ n * conePlus P A =
        qgtPlus P A C ^ n * conePlus P A ∧
      conePlus P A * genV P A C ^ n =
        conePlus P A * qgtMinus P A C ^ n) ∧
    (qgtMinus P A C ^ n * coneMinus P C =
        coneMinus P C * qgtPlus P A C ^ n ∧
      genV P A C ^ n * coneMinus P C =
        qgtMinus P A C ^ n * coneMinus P C ∧
      coneMinus P C * genV P A C ^ n =
        coneMinus P C * qgtPlus P A C ^ n) := by
  have h1 := peirce_push_pull_one hP A C
  rcases h1 with ⟨⟨hQpNp, hVNp, hNpV, _, _⟩, ⟨hQmNm, hVNm, hNmV, _, _⟩⟩
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rcases ih with ⟨⟨ih1, ih2, ih3⟩, ⟨ih4, ih5, ih6⟩⟩
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · calc
        qgtPlus P A C ^ (k + 1) * conePlus P A
          = qgtPlus P A C ^ k * (qgtPlus P A C * conePlus P A) := by
            rw [pow_succ, mul_assoc]
        _ = (qgtPlus P A C ^ k * conePlus P A) * qgtMinus P A C := by
            rw [hQpNp, ← mul_assoc]
        _ = conePlus P A * qgtMinus P A C ^ (k + 1) := by
            rw [ih1, mul_assoc, ← pow_succ]
    · calc
        genV P A C ^ (k + 1) * conePlus P A
          = genV P A C ^ k * (genV P A C * conePlus P A) := by
            rw [pow_succ, mul_assoc]
        _ = genV P A C ^ k * (qgtPlus P A C * conePlus P A) := by
            rw [hVNp]
        _ = (genV P A C ^ k * conePlus P A) * qgtMinus P A C := by
            rw [hQpNp, ← mul_assoc]
        _ = (qgtPlus P A C ^ k * conePlus P A) * qgtMinus P A C := by
            rw [ih2]
        _ = qgtPlus P A C ^ k * (qgtPlus P A C * conePlus P A) := by
            rw [mul_assoc, ← hQpNp]
        _ = qgtPlus P A C ^ (k + 1) * conePlus P A := by
            rw [← mul_assoc, ← pow_succ]
    · calc
        conePlus P A * genV P A C ^ (k + 1)
          = (conePlus P A * genV P A C ^ k) * genV P A C := by
            rw [pow_succ, ← mul_assoc]
        _ = (conePlus P A * qgtMinus P A C ^ k) * genV P A C := by
            rw [ih3]
        _ = qgtPlus P A C ^ k * (conePlus P A * genV P A C) := by
            rw [← ih1, mul_assoc]
        _ = qgtPlus P A C ^ k * (conePlus P A * qgtMinus P A C) := by
            rw [hNpV]
        _ = conePlus P A * qgtMinus P A C ^ (k + 1) := by
            rw [← mul_assoc, ih1, mul_assoc, ← pow_succ]
    · calc
        qgtMinus P A C ^ (k + 1) * coneMinus P C
          = qgtMinus P A C ^ k * (qgtMinus P A C * coneMinus P C) := by
            rw [pow_succ, mul_assoc]
        _ = (qgtMinus P A C ^ k * coneMinus P C) * qgtPlus P A C := by
            rw [hQmNm, ← mul_assoc]
        _ = coneMinus P C * qgtPlus P A C ^ (k + 1) := by
            rw [ih4, mul_assoc, ← pow_succ]
    · calc
        genV P A C ^ (k + 1) * coneMinus P C
          = genV P A C ^ k * (genV P A C * coneMinus P C) := by
            rw [pow_succ, mul_assoc]
        _ = genV P A C ^ k * (qgtMinus P A C * coneMinus P C) := by
            rw [hVNm]
        _ = (genV P A C ^ k * coneMinus P C) * qgtPlus P A C := by
            rw [hQmNm, ← mul_assoc]
        _ = (qgtMinus P A C ^ k * coneMinus P C) * qgtPlus P A C := by
            rw [ih5]
        _ = qgtMinus P A C ^ k * (qgtMinus P A C * coneMinus P C) := by
            rw [mul_assoc, ← hQmNm]
        _ = qgtMinus P A C ^ (k + 1) * coneMinus P C := by
            rw [← mul_assoc, ← pow_succ]
    · calc
        coneMinus P C * genV P A C ^ (k + 1)
          = (coneMinus P C * genV P A C ^ k) * genV P A C := by
            rw [pow_succ, ← mul_assoc]
        _ = (coneMinus P C * qgtPlus P A C ^ k) * genV P A C := by
            rw [ih6]
        _ = qgtMinus P A C ^ k * (coneMinus P C * genV P A C) := by
            rw [← ih4, mul_assoc]
        _ = qgtMinus P A C ^ k * (coneMinus P C * qgtPlus P A C) := by
            rw [hNmV]
        _ = coneMinus P C * qgtPlus P A C ^ (k + 1) := by
            rw [← mul_assoc, ih4, mul_assoc, ← pow_succ]

-- theorem-class: constructive endpoint
/-- **Stage `𝔓₄` Theorem (`stage_P4_push_pull_intertwiner_and_resolvent_equivariance`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Bergman Kernel Push–Pull Identities**:
   * `(1 - qgtPlus P A C) * conePlus P A =
        conePlus P A * (1 - qgtMinus P A C)`,
   * `(1 - genV P A C) * conePlus P A =
        (1 - qgtPlus P A C) * conePlus P A`,
   * `conePlus P A * (1 - genV P A C) =
        conePlus P A * (1 - qgtMinus P A C)`,
   * `(1 - qgtMinus P A C) * coneMinus P C =
        coneMinus P C * (1 - qgtPlus P A C)`.
2. **Exact Resolvent Push–Pull Intertwining (`(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ N_+`)**:
   For any units `U_plus U_minus U_V : Bˣ` satisfying `(U_plus : B) = 1 - qgtPlus P A C`,
   `(U_minus : B) = 1 - qgtMinus P A C`, and `(U_V : B) = 1 - genV P A C`:
   * `(↑U_plus⁻¹ : B) * conePlus P A = conePlus P A * (↑U_minus⁻¹ : B)`,
   * `(↑U_V⁻¹ : B) * conePlus P A = (↑U_plus⁻¹ : B) * conePlus P A`,
   * `conePlus P A * (↑U_V⁻¹ : B) = conePlus P A * (↑U_minus⁻¹ : B)`,
   * `(↑U_minus⁻¹ : B) * coneMinus P C = coneMinus P C * (↑U_plus⁻¹ : B)`,
   * `(↑U_V⁻¹ : B) * coneMinus P C = (↑U_minus⁻¹ : B) * coneMinus P C`. -/
theorem stage_P4_push_pull_intertwiner_and_resolvent_equivariance
    {P : B} (hP : P * P = P) (A C : B)
    (U_plus U_minus U_V : Bˣ)
    (hUp : (U_plus : B) = 1 - qgtPlus P A C)
    (hUm : (U_minus : B) = 1 - qgtMinus P A C)
    (hUV : (U_V : B) = 1 - genV P A C) :
    -- (1) Bergman kernel push-pull identities
    ((1 - qgtPlus P A C) * conePlus P A =
        conePlus P A * (1 - qgtMinus P A C) ∧
      (1 - genV P A C) * conePlus P A =
        (1 - qgtPlus P A C) * conePlus P A ∧
      conePlus P A * (1 - genV P A C) =
        conePlus P A * (1 - qgtMinus P A C) ∧
      (1 - qgtMinus P A C) * coneMinus P C =
        coneMinus P C * (1 - qgtPlus P A C)) ∧
    -- (2) Resolvent push-pull intertwining across U_plus⁻¹, U_minus⁻¹, and U_V⁻¹
    ((↑U_plus⁻¹ : B) * conePlus P A = conePlus P A * (↑U_minus⁻¹ : B) ∧
      (↑U_V⁻¹ : B) * conePlus P A = (↑U_plus⁻¹ : B) * conePlus P A ∧
      conePlus P A * (↑U_V⁻¹ : B) = conePlus P A * (↑U_minus⁻¹ : B) ∧
      (↑U_minus⁻¹ : B) * coneMinus P C = coneMinus P C * (↑U_plus⁻¹ : B) ∧
      (↑U_V⁻¹ : B) * coneMinus P C = (↑U_minus⁻¹ : B) * coneMinus P C) := by
  have h1 :
      (1 - qgtPlus P A C) * conePlus P A =
        conePlus P A * (1 - qgtMinus P A C) := by
    dsimp [qgtPlus, qgtMinus]; peirce_nf hP
  have h2 :
      (1 - genV P A C) * conePlus P A =
        (1 - qgtPlus P A C) * conePlus P A := by
    dsimp [qgtPlus]; peirce_nf hP
  have h3 :
      conePlus P A * (1 - genV P A C) =
        conePlus P A * (1 - qgtMinus P A C) := by
    dsimp [qgtMinus]; peirce_nf hP
  have h4 :
      (1 - qgtMinus P A C) * coneMinus P C =
        coneMinus P C * (1 - qgtPlus P A C) := by
    dsimp [qgtPlus, qgtMinus]; peirce_nf hP
  have h5 :
      (1 - genV P A C) * coneMinus P C =
        (1 - qgtMinus P A C) * coneMinus P C := by
    dsimp [qgtMinus]; peirce_nf hP
  have hUpUm : (U_plus : B) * conePlus P A = conePlus P A * (U_minus : B) := by
    rw [hUp, hUm, h1]
  have hUVUp : (U_V : B) * conePlus P A = (U_plus : B) * conePlus P A := by
    rw [hUV, hUp, h2]
  have hUVUmR : conePlus P A * (U_V : B) = conePlus P A * (U_minus : B) := by
    rw [hUV, hUm, h3]
  have hUmUp : (U_minus : B) * coneMinus P C = coneMinus P C * (U_plus : B) := by
    rw [hUm, hUp, h4]
  have hUVUm : (U_V : B) * coneMinus P C = (U_minus : B) * coneMinus P C := by
    rw [hUV, hUm, h5]
  have hInv1 : (↑U_plus⁻¹ : B) * conePlus P A = conePlus P A * (↑U_minus⁻¹ : B) := by
    calc
      (↑U_plus⁻¹ : B) * conePlus P A
        = (↑U_plus⁻¹ : B) * (conePlus P A * ((U_minus : B) * (↑U_minus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_plus⁻¹ : B) * (conePlus P A * (U_minus : B)) * (↑U_minus⁻¹ : B) := by
          noncomm_ring
      _ = ((↑U_plus⁻¹ : B) * (U_plus : B)) * conePlus P A * (↑U_minus⁻¹ : B) := by
          rw [← hUpUm]; noncomm_ring
      _ = conePlus P A * (↑U_minus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
  have hInv2 : (↑U_V⁻¹ : B) * conePlus P A = (↑U_plus⁻¹ : B) * conePlus P A := by
    calc
      (↑U_V⁻¹ : B) * conePlus P A
        = (↑U_V⁻¹ : B) * (conePlus P A * ((U_minus : B) * (↑U_minus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_V⁻¹ : B) * (conePlus P A * (U_minus : B)) * (↑U_minus⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_V⁻¹ : B) * ((U_V : B) * conePlus P A) * (↑U_minus⁻¹ : B) := by
          rw [← hUpUm, ← hUVUp]
      _ = ((↑U_V⁻¹ : B) * (U_V : B)) * conePlus P A * (↑U_minus⁻¹ : B) := by
          noncomm_ring
      _ = conePlus P A * (↑U_minus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (↑U_plus⁻¹ : B) * conePlus P A := hInv1.symm
  have hInv3 : conePlus P A * (↑U_V⁻¹ : B) = conePlus P A * (↑U_minus⁻¹ : B) := by
    calc
      conePlus P A * (↑U_V⁻¹ : B)
        = (((↑U_plus⁻¹ : B) * (U_plus : B)) * conePlus P A) * (↑U_V⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (↑U_plus⁻¹ : B) * ((U_plus : B) * conePlus P A) * (↑U_V⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_plus⁻¹ : B) * (conePlus P A * (U_V : B)) * (↑U_V⁻¹ : B) := by
          rw [hUpUm, ← hUVUmR]
      _ = (↑U_plus⁻¹ : B) * conePlus P A * ((U_V : B) * (↑U_V⁻¹ : B)) := by
          noncomm_ring
      _ = (↑U_plus⁻¹ : B) * conePlus P A := by
          rw [Units.mul_inv, mul_one]
      _ = conePlus P A * (↑U_minus⁻¹ : B) := hInv1
  have hInv4 : (↑U_minus⁻¹ : B) * coneMinus P C = coneMinus P C * (↑U_plus⁻¹ : B) := by
    calc
      (↑U_minus⁻¹ : B) * coneMinus P C
        = (↑U_minus⁻¹ : B) * (coneMinus P C * ((U_plus : B) * (↑U_plus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_minus⁻¹ : B) * (coneMinus P C * (U_plus : B)) * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = ((↑U_minus⁻¹ : B) * (U_minus : B)) * coneMinus P C * (↑U_plus⁻¹ : B) := by
          rw [← hUmUp]; noncomm_ring
      _ = coneMinus P C * (↑U_plus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
  have hInv5 : (↑U_V⁻¹ : B) * coneMinus P C = (↑U_minus⁻¹ : B) * coneMinus P C := by
    calc
      (↑U_V⁻¹ : B) * coneMinus P C
        = (↑U_V⁻¹ : B) * (coneMinus P C * ((U_plus : B) * (↑U_plus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_V⁻¹ : B) * (coneMinus P C * (U_plus : B)) * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_V⁻¹ : B) * ((U_V : B) * coneMinus P C) * (↑U_plus⁻¹ : B) := by
          rw [← hUmUp, ← hUVUm]
      _ = ((↑U_V⁻¹ : B) * (U_V : B)) * coneMinus P C * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = coneMinus P C * (↑U_plus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (↑U_minus⁻¹ : B) * coneMinus P C := hInv4.symm
  exact ⟨⟨h1, h2, h3, h4⟩, ⟨hInv1, hInv2, hInv3, hInv4, hInv5⟩⟩

/-- Construct all three Peirce resolvent units from the single nilpotence
hypothesis on the metric carrier `V`.  The corner Gramians are nilpotent because
`Q₊ * V^k = Q₊^(k+1)` and `Q₋ * V^k = Q₋^(k+1)`; this derives the inverse
witnesses needed by the conditional push-pull theorem instead of assuming them.
Nilpotence of `V` is an explicit sufficient condition, not a property of all
Peirce data. -/
theorem exists_peirce_resolvent_units_of_nilpotent_metric
    {P : B} (hP : P * P = P) (A C : B) (n : ℕ)
    (hV : genV P A C ^ n = 0) :
    ∃ U_plus U_minus U_V : Bˣ,
      (U_plus : B) = 1 - qgtPlus P A C ∧
      (U_minus : B) = 1 - qgtMinus P A C ∧
      (U_V : B) = 1 - genV P A C := by
  let Qp := qgtPlus P A C
  let Qm := qgtMinus P A C
  let V := genV P A C
  have hQpV' : Qp * V = Qp * Qp := by
    dsimp [Qp, V, qgtPlus]
    peirce_nf hP
  have hQpV : Qp * V = Qp ^ 2 := by
    rw [sq, hQpV']
  have hQmV' : Qm * V = Qm * Qm := by
    dsimp [Qm, V, qgtMinus]
    peirce_nf hP
  have hQmV : Qm * V = Qm ^ 2 := by
    rw [sq, hQmV']
  have hQpIter : ∀ k : ℕ, Qp * V ^ k = Qp ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          Qp * V ^ (k + 1) = (Qp * V ^ k) * V := by rw [pow_succ, ← mul_assoc]
          _ = Qp ^ (k + 1) * V := by rw [ih]
          _ = Qp ^ k * (Qp * V) := by rw [pow_succ, mul_assoc]
          _ = Qp ^ k * (Qp * Qp) := by rw [hQpV']
          _ = Qp ^ (k + 1 + 1) := by rw [← mul_assoc, ← pow_succ, ← pow_succ]
  have hQmIter : ∀ k : ℕ, Qm * V ^ k = Qm ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          Qm * V ^ (k + 1) = (Qm * V ^ k) * V := by rw [pow_succ, ← mul_assoc]
          _ = Qm ^ (k + 1) * V := by rw [ih]
          _ = Qm ^ k * (Qm * V) := by rw [pow_succ, mul_assoc]
          _ = Qm ^ k * (Qm * Qm) := by rw [hQmV']
          _ = Qm ^ (k + 1 + 1) := by rw [← mul_assoc, ← pow_succ, ← pow_succ]
  have hQpNil : Qp ^ (n + 1) = 0 := by
    have h := hQpIter n
    rw [hV, mul_zero] at h
    exact h.symm
  have hQmNil : Qm ^ (n + 1) = 0 := by
    have h := hQmIter n
    rw [hV, mul_zero] at h
    exact h.symm
  let U_plus : Bˣ :=
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent
      (x := Qp) hQpNil
  let U_minus : Bˣ :=
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent
      (x := Qm) hQmNil
  let U_V : Bˣ :=
    InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent
      (x := V) hV
  refine ⟨U_plus, U_minus, U_V, ?_, ?_, ?_⟩
  · simp [U_plus, Qp,
      InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent]
  · simp [U_minus, Qm,
      InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent]
  · simp [U_V, V,
      InfoGeometry.OperatorAlgebra.OperatorDirichlet.nilpotentResolvent]

/-- Ordered non-commutative Operator Möbius fractional transition `(c + d * f) * R_den`
in an associative ring `B`, where `R_den` is a right inverse to the Möbius denominator `a + b * f`. -/
def operatorMoebiusRingTransition (c d f R_den : B) : B :=
  (c + d * f) * R_den

-- theorem-class: constructive endpoint
/-- **Operator Möbius `↔` Push–Pull Legendre Equivalence & Left/Right-Absorptive Chart Semigroups
(`stage_P4_left_right_absorptive_chart_semigroups_and_moebius_legendre_identity`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Left-Absorptive Dual Chart Semigroup (`P_-(C₁) P_-(C₂) = P_-(C₁)`)**:
   * `superGrassmannDualChart P C₁ * superGrassmannDualChart P C₂ = superGrassmannDualChart P C₁`,
   * `comm (superGrassmannDualChart P C₁) (superGrassmannDualChart P C₂) = coneMinus P C₁ - coneMinus P C₂`,
   * `comm (superGrassmannDualChart P C₁) (superGrassmannDualChart P C₂) = 0 ↔ coneMinus P C₁ = coneMinus P C₂`.
2. **Right-Absorptive Primal Chart Semigroup (`P_+(A₁) P_+(A₂) = P_+(A₂)`)**:
   * `superGrassmannPrimalChart P A₁ * superGrassmannPrimalChart P A₂ = superGrassmannPrimalChart P A₂`,
   * `comm (superGrassmannPrimalChart P A₁) (superGrassmannPrimalChart P A₂) = conePlus P A₂ - conePlus P A₁`,
   * `comm (superGrassmannPrimalChart P A₁) (superGrassmannPrimalChart P A₂) = 0 ↔ conePlus P A₁ = conePlus P A₂`.
3. **Exact Equivalence of the Operator Möbius Transition and the Amari Legendre Coordinate (`𝔊₃ ⋈ 𝔓₄`)**:
   Evaluating the Operator Möbius denominator `a + b * f` at the unipotent dual dressing
   `(a, b, c, d) = (1, -N_-, 0, 1)` on the primal chart `f = N_+` yields `1 - Q_-`:
   * `1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C`,
   * Whenever `(U_plus : B) = 1 - qgtPlus P A C`, `(U_minus : B) = 1 - qgtMinus P A C`, and
     `(U_V : B) = 1 - genV P A C`, the Operator Möbius fractional transition
     `operatorMoebiusRingTransition 0 1 (conePlus P A) (↑U_minus⁻¹ : B)` equals the right resolvent
     action `N_+ U_-⁻¹`, the left Bergman resolvent action `U_+⁻¹ N_+` (the Amari Legendre-dual
     expectation coordinate `η_-`), and the symmetric Fisher resolvent action `U_V⁻¹ N_+`:
     $$\mathcal{M}_{(1, -N_-, 0, 1)}(N_+; U_-^{-1}) = N_+ U_-^{-1} = U_+^{-1} N_+ = U_V^{-1} N_+.$$ -/
theorem stage_P4_left_right_absorptive_chart_semigroups_and_moebius_legendre_identity
    {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ : B)
    (U_plus U_minus U_V : Bˣ)
    (hU_plus : (U_plus : B) = 1 - qgtPlus P A C)
    (hU_minus : (U_minus : B) = 1 - qgtMinus P A C)
    (hU_V : (U_V : B) = 1 - genV P A C) :
    -- (1) Left-absorptive dual chart semigroup
    (superGrassmannDualChart P C₁ * superGrassmannDualChart P C₂ = superGrassmannDualChart P C₁ ∧
      OperatorAlgebra.PeirceSpine.comm (superGrassmannDualChart P C₁) (superGrassmannDualChart P C₂) =
        coneMinus P C₁ - coneMinus P C₂ ∧
      (OperatorAlgebra.PeirceSpine.comm (superGrassmannDualChart P C₁) (superGrassmannDualChart P C₂) = 0 ↔
        coneMinus P C₁ = coneMinus P C₂)) ∧
    -- (2) Right-absorptive primal chart semigroup
    (superGrassmannPrimalChart P A₁ * superGrassmannPrimalChart P A₂ = superGrassmannPrimalChart P A₂ ∧
      OperatorAlgebra.PeirceSpine.comm (superGrassmannPrimalChart P A₁) (superGrassmannPrimalChart P A₂) =
        conePlus P A₂ - conePlus P A₁ ∧
      (OperatorAlgebra.PeirceSpine.comm (superGrassmannPrimalChart P A₁) (superGrassmannPrimalChart P A₂) = 0 ↔
        conePlus P A₁ = conePlus P A₂)) ∧
    -- (3) Operator Möbius ↔ Push–Pull Legendre Expectation Coordinate identity
    (1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) (↑U_minus⁻¹ : B) =
        conePlus P A * (↑U_minus⁻¹ : B) ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) (↑U_minus⁻¹ : B) =
        (↑U_plus⁻¹ : B) * conePlus P A ∧
      operatorMoebiusRingTransition 0 1 (conePlus P A) (↑U_minus⁻¹ : B) =
        (↑U_V⁻¹ : B) * conePlus P A) := by
  have hDualMul :
      superGrassmannDualChart P C₁ * superGrassmannDualChart P C₂ = superGrassmannDualChart P C₁ := by
    dsimp [superGrassmannDualChart, amariExpMinus]
    peirce_nf hP
  have hDualComm :
      OperatorAlgebra.PeirceSpine.comm (superGrassmannDualChart P C₁) (superGrassmannDualChart P C₂) =
        coneMinus P C₁ - coneMinus P C₂ := by
    dsimp [superGrassmannDualChart, amariExpMinus, OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  have hPrimalMul :
      superGrassmannPrimalChart P A₁ * superGrassmannPrimalChart P A₂ = superGrassmannPrimalChart P A₂ := by
    dsimp [superGrassmannPrimalChart, amariExpPlus]
    peirce_nf hP
  have hPrimalComm :
      OperatorAlgebra.PeirceSpine.comm (superGrassmannPrimalChart P A₁) (superGrassmannPrimalChart P A₂) =
        conePlus P A₂ - conePlus P A₁ := by
    dsimp [superGrassmannPrimalChart, amariExpPlus, OperatorAlgebra.PeirceSpine.comm]
    peirce_nf hP
  have hDenom : 1 + (-coneMinus P C) * conePlus P A = 1 - qgtMinus P A C := by
    dsimp [qgtMinus]
    noncomm_ring
  have hMoeb :
      operatorMoebiusRingTransition 0 1 (conePlus P A) (↑U_minus⁻¹ : B) =
        conePlus P A * (↑U_minus⁻¹ : B) := by
    dsimp [operatorMoebiusRingTransition]
    noncomm_ring
  have hP4 :=
    stage_P4_push_pull_intertwiner_and_resolvent_equivariance hP A C
      U_plus U_minus U_V hU_plus hU_minus hU_V
  refine ⟨⟨hDualMul, hDualComm, ?_⟩, ⟨hPrimalMul, hPrimalComm, ?_⟩,
    ⟨hDenom, hMoeb, hMoeb.trans hP4.2.1.symm,
     hMoeb.trans (hP4.2.1.symm.trans hP4.2.2.1.symm)⟩⟩
  · rw [hDualComm, sub_eq_zero]
  · rw [hPrimalComm, sub_eq_zero, eq_comm]

end StageP4PushPullIntertwinerAndResolventEquivariance

/-! ===========================================================================
    Section 6: Stage `𝔓₅` — Legendre–Schur Differential Collapse & The
    Hua–Bergman–Dikin Para-Kähler Operator Metric
    =========================================================================== -/

section StageP5LegendreSchurDifferentialAndHuaBergmanDikinMetric

variable {B : Type*} [Ring B]

/-- The **Legendre–Schur Expectation Coordinate**
`legendreSchurCoord U_plus P A := (↑U_plus⁻¹ : B) * conePlus P A`. -/
def legendreSchurCoord (U_plus : Bˣ) (P A : B) : B :=
  (↑U_plus⁻¹ : B) * conePlus P A

/-- The **Two-Term Leibniz Differential of the Legendre–Schur Coordinate** along a
primal variation `dN_+ = conePlus P dA`:
`legendreSchurDifferential U_plus P A C dA :=
  (↑U_plus⁻¹ : B) * N_+(dA) +
    (↑U_plus⁻¹ : B) * N_+(dA) * N_-(C) * (↑U_plus⁻¹ : B) * N_+(A)`. -/
def legendreSchurDifferential (U_plus : Bˣ) (P A C dA : B) : B :=
  (↑U_plus⁻¹ : B) * conePlus P dA +
    (↑U_plus⁻¹ : B) * conePlus P dA * coneMinus P C *
      (↑U_plus⁻¹ : B) * conePlus P A

/-- The **Hua–Bergman–Dikin Para-Kähler Operator Metric Tensor**
`huaBergmanDikinMetric U_plus U_minus P dA dC :=
  (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) * coneMinus P dC`. -/
def huaBergmanDikinMetric (U_plus U_minus : Bˣ) (P dA dC : B) : B :=
  (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) * coneMinus P dC

-- theorem-class: constructive endpoint
/-- **Stage `𝔓₅` Theorem
(`stage_P5_legendre_schur_differential_and_hua_bergman_dikin_metric`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`, let `U_plus U_minus U_V : Bˣ`
satisfy `(U_plus : B) = 1 - qgtPlus P A C`,
`(U_minus : B) = 1 - qgtMinus P A C`, and `(U_V : B) = 1 - genV P A C`:
1. **Sheet-Projector Commutation & Resolvent Absorption Identities**:
   * `(↑U_V⁻¹ : B) * P = (↑U_plus⁻¹ : B) * P` and `(1 - P) * (↑U_V⁻¹ : B) = (1 - P) * (↑U_minus⁻¹ : B)`,
   * `1 + qgtMinus P A C * (↑U_minus⁻¹ : B) = (↑U_minus⁻¹ : B)`,
   * `1 + qgtPlus P A C * (↑U_plus⁻¹ : B) = (↑U_plus⁻¹ : B)`.
2. **Exact Push–Pull Collapse of the Two-Term Legendre–Schur Differential**:
   * `legendreSchurDifferential U_plus P A C dA =
        (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B)`,
   * `legendreSchurDifferential U_plus P A C dA =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B)`.
3. **Hua–Bergman–Dikin Para-Kähler Operator Metric**:
   * `legendreSchurDifferential U_plus P A C dA * coneMinus P dC =
        huaBergmanDikinMetric U_plus U_minus P dA dC`,
   * `huaBergmanDikinMetric U_plus U_minus P dA dC =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) * coneMinus P dC`,
   * **Origin Reduction (`U_plus = U_minus = 1`)**:
     `huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC`.
4. **Bridge to Native Analytic Log-Det Fréchet Hessian (`OperatorLogDetDikinGeometry.hessianMap_negLogDet`)**:
   For any invertible complex matrix `M : Matrix n n ℂ` (`IsUnit M`) and directions `K, H`:
   `hessianMap negLogDet M K H = (Matrix.trace (M⁻¹ * K * M⁻¹ * H)).re`. -/
theorem stage_P5_legendre_schur_differential_and_hua_bergman_dikin_metric
    {P : B} (hP : P * P = P) (A C dA dC : B)
    (U_plus U_minus U_V : Bˣ)
    (hUp : (U_plus : B) = 1 - qgtPlus P A C)
    (hUm : (U_minus : B) = 1 - qgtMinus P A C)
    (hUV : (U_V : B) = 1 - genV P A C)
    {n : Type*} [Fintype n] [DecidableEq n]
    (M K H : Matrix n n ℂ) (hM : IsUnit M) :
    -- (1) Sheet-projector resolvent equivalence & absorption identities
    ((↑U_V⁻¹ : B) * P = (↑U_plus⁻¹ : B) * P ∧
      (1 - P) * (↑U_V⁻¹ : B) = (1 - P) * (↑U_minus⁻¹ : B) ∧
      1 + qgtMinus P A C * (↑U_minus⁻¹ : B) = (↑U_minus⁻¹ : B) ∧
      1 + qgtPlus P A C * (↑U_plus⁻¹ : B) = (↑U_plus⁻¹ : B)) ∧
    -- (2) Exact Push-Pull collapse of the two-term Legendre-Schur differential
    (legendreSchurDifferential U_plus P A C dA =
        (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) ∧
      legendreSchurDifferential U_plus P A C dA =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B)) ∧
    -- (3) Hua-Bergman-Dikin Para-Kähler operator metric & origin reduction
    (legendreSchurDifferential U_plus P A C dA * coneMinus P dC =
        huaBergmanDikinMetric U_plus U_minus P dA dC ∧
      huaBergmanDikinMetric U_plus U_minus P dA dC =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) * coneMinus P dC ∧
      huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC) ∧
    -- (4) Native Fréchet log-det Hessian bridge
    hessianMap negLogDet M K H = (Matrix.trace (M⁻¹ * K * M⁻¹ * H)).re := by
  have hP4 :=
    stage_P4_push_pull_intertwiner_and_resolvent_equivariance
      hP A C U_plus U_minus U_V hUp hUm hUV
  rcases hP4 with ⟨_, ⟨hInv1, _, _, _, _⟩⟩
  have hUpP : (U_plus : B) * P = P * (U_plus : B) := by
    rw [hUp]; dsimp [qgtPlus]; peirce_nf hP
  have hUVUpP : (U_V : B) * P = (U_plus : B) * P := by
    rw [hUV, hUp]; dsimp [qgtPlus]; peirce_nf hP
  have hUm1mP : (U_minus : B) * (1 - P) = (1 - P) * (U_minus : B) := by
    rw [hUm]; dsimp [qgtMinus]; peirce_nf hP
  have hUVUm1mP : (1 - P) * (U_V : B) = (1 - P) * (U_minus : B) := by
    rw [hUV, hUm]; dsimp [qgtMinus]; peirce_nf hP
  have hInvUVUpP : (↑U_V⁻¹ : B) * P = (↑U_plus⁻¹ : B) * P := by
    calc
      (↑U_V⁻¹ : B) * P
        = (↑U_V⁻¹ : B) * (P * ((U_plus : B) * (↑U_plus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_V⁻¹ : B) * (P * (U_plus : B)) * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_V⁻¹ : B) * ((U_V : B) * P) * (↑U_plus⁻¹ : B) := by
          rw [← hUpP, ← hUVUpP]
      _ = ((↑U_V⁻¹ : B) * (U_V : B)) * P * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = P * (↑U_plus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (((↑U_plus⁻¹ : B) * (U_plus : B)) * P) * (↑U_plus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (↑U_plus⁻¹ : B) * ((U_plus : B) * P) * (↑U_plus⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_plus⁻¹ : B) * P * ((U_plus : B) * (↑U_plus⁻¹ : B)) := by
          rw [hUpP]; noncomm_ring
      _ = (↑U_plus⁻¹ : B) * P := by
          rw [Units.mul_inv, mul_one]
  have hInvUVUm1mP : (1 - P) * (↑U_V⁻¹ : B) = (1 - P) * (↑U_minus⁻¹ : B) := by
    calc
      (1 - P) * (↑U_V⁻¹ : B)
        = (((↑U_minus⁻¹ : B) * (U_minus : B)) * (1 - P)) * (↑U_V⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
      _ = (↑U_minus⁻¹ : B) * ((U_minus : B) * (1 - P)) * (↑U_V⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_minus⁻¹ : B) * ((1 - P) * (U_V : B)) * (↑U_V⁻¹ : B) := by
          rw [hUm1mP, ← hUVUm1mP]
      _ = (↑U_minus⁻¹ : B) * (1 - P) * ((U_V : B) * (↑U_V⁻¹ : B)) := by
          noncomm_ring
      _ = (↑U_minus⁻¹ : B) * (1 - P) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_minus⁻¹ : B) * ((1 - P) * ((U_minus : B) * (↑U_minus⁻¹ : B))) := by
          rw [Units.mul_inv, mul_one]
      _ = (↑U_minus⁻¹ : B) * ((1 - P) * (U_minus : B)) * (↑U_minus⁻¹ : B) := by
          noncomm_ring
      _ = ((↑U_minus⁻¹ : B) * (U_minus : B)) * (1 - P) * (↑U_minus⁻¹ : B) := by
          rw [← hUm1mP]; noncomm_ring
      _ = (1 - P) * (↑U_minus⁻¹ : B) := by
          rw [Units.inv_mul, one_mul]
  have hAbsUm : 1 + qgtMinus P A C * (↑U_minus⁻¹ : B) = (↑U_minus⁻¹ : B) := by
    have hMul : ((U_minus : B) + qgtMinus P A C) * (↑U_minus⁻¹ : B) = (↑U_minus⁻¹ : B) := by
      rw [hUm]
      noncomm_ring
    calc
      1 + qgtMinus P A C * (↑U_minus⁻¹ : B)
        = (U_minus : B) * (↑U_minus⁻¹ : B) + qgtMinus P A C * (↑U_minus⁻¹ : B) := by
          rw [Units.mul_inv]
      _ = ((U_minus : B) + qgtMinus P A C) * (↑U_minus⁻¹ : B) := by
          rw [← add_mul]
      _ = (↑U_minus⁻¹ : B) := hMul
  have hAbsUp : 1 + qgtPlus P A C * (↑U_plus⁻¹ : B) = (↑U_plus⁻¹ : B) := by
    have hMul : ((U_plus : B) + qgtPlus P A C) * (↑U_plus⁻¹ : B) = (↑U_plus⁻¹ : B) := by
      rw [hUp]
      noncomm_ring
    calc
      1 + qgtPlus P A C * (↑U_plus⁻¹ : B)
        = (U_plus : B) * (↑U_plus⁻¹ : B) + qgtPlus P A C * (↑U_plus⁻¹ : B) := by
          rw [Units.mul_inv]
      _ = ((U_plus : B) + qgtPlus P A C) * (↑U_plus⁻¹ : B) := by
          rw [← add_mul]
      _ = (↑U_plus⁻¹ : B) := hMul
  have hDiff1 :
      legendreSchurDifferential U_plus P A C dA =
        (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) := by
    dsimp [legendreSchurDifferential]
    calc
      (↑U_plus⁻¹ : B) * conePlus P dA +
          (↑U_plus⁻¹ : B) * conePlus P dA * coneMinus P C *
            (↑U_plus⁻¹ : B) * conePlus P A
        = (↑U_plus⁻¹ : B) * conePlus P dA * 1 +
            (↑U_plus⁻¹ : B) * conePlus P dA * coneMinus P C *
              ((↑U_plus⁻¹ : B) * conePlus P A) := by
          noncomm_ring
      _ = (↑U_plus⁻¹ : B) * conePlus P dA * 1 +
            (↑U_plus⁻¹ : B) * conePlus P dA *
              (coneMinus P C * conePlus P A) * (↑U_minus⁻¹ : B) := by
          rw [hInv1]; noncomm_ring
      _ = (↑U_plus⁻¹ : B) * conePlus P dA *
            (1 + qgtMinus P A C * (↑U_minus⁻¹ : B)) := by
          dsimp [qgtMinus]; noncomm_ring
      _ = (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) := by
          rw [hAbsUm]
  have hPNpdA : P * conePlus P dA = conePlus P dA := by peirce_nf hP
  have hNpdA1mP : conePlus P dA * (1 - P) = conePlus P dA := by peirce_nf hP
  have hCorner : conePlus P dA = P * (conePlus P dA * (1 - P)) := by
    calc
      conePlus P dA = P * conePlus P dA := hPNpdA.symm
      _ = P * (conePlus P dA * (1 - P)) := by rw [hNpdA1mP]
  have hDiff2 :
      legendreSchurDifferential U_plus P A C dA =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) := by
    rw [hDiff1]
    calc
      (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B)
        = (↑U_plus⁻¹ : B) * (P * (conePlus P dA * (1 - P))) * (↑U_minus⁻¹ : B) := by
          congr 2
      _ = ((↑U_plus⁻¹ : B) * P) * conePlus P dA * ((1 - P) * (↑U_minus⁻¹ : B)) := by
          noncomm_ring
      _ = ((↑U_V⁻¹ : B) * P) * conePlus P dA * ((1 - P) * (↑U_V⁻¹ : B)) := by
          rw [← hInvUVUpP, ← hInvUVUm1mP]
      _ = (↑U_V⁻¹ : B) * (P * (conePlus P dA * (1 - P))) * (↑U_V⁻¹ : B) := by
          noncomm_ring
      _ = (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) := by
          congr 2
          exact hCorner.symm
  have hHua1 :
      legendreSchurDifferential U_plus P A C dA * coneMinus P dC =
        huaBergmanDikinMetric U_plus U_minus P dA dC := by
    rw [hDiff1]; rfl
  have hHua2 :
      huaBergmanDikinMetric U_plus U_minus P dA dC =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) * coneMinus P dC := by
    rw [← hHua1, hDiff2]
  have hHua0 :
      huaBergmanDikinMetric 1 1 P dA dC = qgtPlus P dA dC := by
    dsimp [huaBergmanDikinMetric, qgtPlus]
    simp
  exact ⟨⟨hInvUVUpP, hInvUVUm1mP, hAbsUm, hAbsUp⟩,
    ⟨hDiff1, hDiff2⟩,
    ⟨hHua1, hHua2, hHua0⟩,
    hessianMap_negLogDet M K H hM⟩

end StageP5LegendreSchurDifferentialAndHuaBergmanDikinMetric

/-! ===========================================================================
    Section 7: Stage `𝔓₆` — Super-LU Bergman Berezinian Factorization
    (`(1 - Q_+)(1 - Q_-) = 1 - V`), `2 × 2` Super-LU Berezinian, & Chiral-Weighted
    Truncated Log-Berezinian Potential
    =========================================================================== -/

section StageP6SuperLUBergmanBerezinianAndSplitFactorization

variable {B : Type*} [Ring B]

/-- Second-order truncated upper-sheet log-Berezinian potential
`paraKahlerLogPotentialPlus P A C := Q_+ + ½ Q_+²`. -/
def paraKahlerLogPotentialPlus [Algebra ℚ B] (P A C : B) : B :=
  qgtPlus P A C + (1 / 2 : ℚ) • (qgtPlus P A C * qgtPlus P A C)

/-- Second-order truncated lower-sheet log-Berezinian potential
`paraKahlerLogPotentialMinus P A C := Q_- + ½ Q_-²`. -/
def paraKahlerLogPotentialMinus [Algebra ℚ B] (P A C : B) : B :=
  qgtMinus P A C + (1 / 2 : ℚ) • (qgtMinus P A C * qgtMinus P A C)

-- theorem-class: constructive endpoint
/-- **Stage `𝔓₆` Theorem (`stage_P6_super_lu_bergman_berezinian_and_split_factorization`)**:
In any noncommutative `[Ring B]` with idempotent `P * P = P`:
1. **Primal & Dual Unipotent Peirce–Gauss Block-Diagonalizations of `1 + Φ = 1 + N_+ + N_-`**:
   * Left-multiplying `1 + genPhi P A C` by `amariExpPlus P (-A) = 1 - N_+(P, A)` and
     right-multiplying by `amariExpMinus P (-C) = 1 - N_-(P, C)` eliminates both off-diagonal
     corners and yields the **Upper Bergman Kernel `1 - Q_+`**:
     `amariExpPlus P (-A) * (1 + genPhi P A C) * amariExpMinus P (-C) =
        1 - qgtPlus P A C`,
   * Left-multiplying `1 + genPhi P A C` by `amariExpMinus P (-C) = 1 - N_-(P, C)` and
     right-multiplying by `amariExpPlus P (-A) = 1 - N_+(P, A)` yields the **Lower Bergman
     Kernel `1 - Q_-`**:
     `amariExpMinus P (-C) * (1 + genPhi P A C) * amariExpPlus P (-A) =
        1 - qgtMinus P A C`.
2. **Commutative Factorization of the Total Bergman Kernel `1 - V`**:
   * `(1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
        1 - genV P A C`,
   * `(1 - qgtMinus P A C) * (1 - qgtPlus P A C) =
        1 - genV P A C`.
3. **Bridge to the `2 × 2` Super-LU Berezinian (`InfoGeometry.Supergeometry.Berezinian`)**:
   For any commutative ring `R` and overlap supermatrix
   `M_chart z w = !![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R`:
   * `InfoGeometry.Supergeometry.Berezinian.berezinian !![1, -z; -w, 1] 1 = 1 - z * w`,
   * `factorL !![1, -z; -w, 1] 1 * factorH !![1, -z; -w, 1] 1 * factorR !![1, -z; -w, 1] 1 =
        !![1, -z; -w, 1]`.
4. **Chiral-Weighted Second-Order Log-Berezinian Potential**:
   Over `[Algebra ℚ B]`:
   * `paraKahlerLogPotentialPlus P A C + paraKahlerLogPotentialMinus P A C =
        genV P A C + (1 / 2 : ℚ) • (genV P A C * genV P A C)`,
   * `invS P * (paraKahlerLogPotentialPlus P A C + paraKahlerLogPotentialMinus P A C) =
        genSig P A C +
          (1 / 2 : ℚ) • (invS P * (genV P A C * genV P A C))`. -/
theorem stage_P6_super_lu_bergman_berezinian_and_split_factorization
    [Algebra ℚ B] {P : B} (hP : P * P = P) (A C : B)
    {R : Type*} [CommRing R] (z w : R) :
    -- (1) Primal & dual unipotent Peirce-Gauss block-diagonalizations of 1 + Φ
    (amariExpPlus P (-A) * (1 + genPhi P A C) * amariExpMinus P (-C) =
        1 - qgtPlus P A C ∧
      amariExpMinus P (-C) * (1 + genPhi P A C) * amariExpPlus P (-A) =
        1 - qgtMinus P A C) ∧
    -- (2) Commutative factorization (1 - Q_+)(1 - Q_-) = 1 - V
    ((1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
        1 - genV P A C ∧
      (1 - qgtMinus P A C) * (1 - qgtPlus P A C) =
        1 - genV P A C) ∧
    -- (3) 2 × 2 Super-LU Berezinian & trifactor decomposition
    (InfoGeometry.Supergeometry.Berezinian.berezinian (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R) 1 =
        1 - z * w ∧
      factorL (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R) 1 *
        factorH (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R) 1 *
        factorR (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R) 1 =
          (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R)) ∧
    -- (4) Chiral-weighted second-order log-Berezinian potential
    (paraKahlerLogPotentialPlus P A C + paraKahlerLogPotentialMinus P A C =
        genV P A C + (1 / 2 : ℚ) • (genV P A C * genV P A C) ∧
      invS P * (paraKahlerLogPotentialPlus P A C + paraKahlerLogPotentialMinus P A C) =
        genSig P A C +
          (1 / 2 : ℚ) • (invS P * (genV P A C * genV P A C))) := by
  have hQ2 :
      qgtPlus P A C * qgtPlus P A C +
        qgtMinus P A C * qgtMinus P A C =
          genV P A C * genV P A C := by
    dsimp [qgtPlus, qgtMinus]; peirce_nf hP
  have hQpQm : qgtPlus P A C + qgtMinus P A C = genV P A C := by
    dsimp [qgtPlus, qgtMinus]; peirce_nf hP
  have hSumPot :
      paraKahlerLogPotentialPlus P A C + paraKahlerLogPotentialMinus P A C =
        genV P A C + (1 / 2 : ℚ) • (genV P A C * genV P A C) := by
    dsimp [paraKahlerLogPotentialPlus, paraKahlerLogPotentialMinus]
    rw [← hQ2, smul_add, ← hQpQm]
    abel
  have hSPV : invS P * genV P A C = genSig P A C := by
    peirce_nf hP
  refine ⟨⟨by dsimp [amariExpPlus, amariExpMinus, qgtPlus]; peirce_nf hP,
           by dsimp [amariExpPlus, amariExpMinus, qgtMinus]; peirce_nf hP⟩,
    ⟨by dsimp [qgtPlus, qgtMinus]; peirce_nf hP,
     by dsimp [qgtPlus, qgtMinus]; peirce_nf hP⟩,
    ⟨by simp [InfoGeometry.Supergeometry.Berezinian.berezinian],
     super_lu_factorization (!![1, -z; -w, 1] : Matrix (Fin 2) (Fin 2) R) 1 (mul_one 1)⟩,
    ⟨hSumPot,
     by
       rw [hSumPot, mul_add, hSPV, mul_smul_comm]⟩⟩

end StageP6SuperLUBergmanBerezinianAndSplitFactorization

/-! ===========================================================================
    Section 8: Stage `𝔓₇` — Master Synthesis Unifying Split-Octonion (`𝕆_s`),
    Super-Grassmannian (`Gr(m|n, p|q)`), and Para-Kähler Amari Operator Geometry
    (`𝔓₁ ≺ … ≺ 𝔓₇`, `𝔒₁ ≺ … ≺ 𝔒₇`, `𝔇₁ ≺ … ≺ 𝔇₇`)
    =========================================================================== -/

-- theorem-class: capstone consumer theorem
/-- **Master Capstone Theorem
(`para_kahler_super_grassmannian_bruhat_push_pull_dikin_master_poset`)**:
Unifies the 7-stage Para-Kähler Super-Grassmannian Poset (`𝔓₁ ≺ … ≺ 𝔓₇`) with
the Split-Octonion Isotropic Circular Poset (`𝔒₁ ≺ … ≺ 𝔒₇`) and First-Quantized
Amari Operator Geometry (`𝔇₁ ≺ … ≺ 𝔇₇`):
1. Strict acyclicity across `ParaKahlerSuperGrassmannianStage`,
   `SplitOctonionIsotropicAmariStage`, and `AmariDuallyFlatOperatorStage`,
2. Unipotent single-chart idempotency (`P_+(A)² = P_+(A)`, `P_-(C)² = P_-(C)`),
   Rung 0 naive linear superposition aporia (`Ψ² - Ψ = V`), and two-chart
   Para-Kähler commutator curvature (`[P_+(A), P_-(C)] = Σ - Φ`),
3. Exact Bruhat-dressed two-chart idempotent
   `P̂(P, A, C) = P + Φ - Σ - V * N_+` with `P̂² = P̂`,
4. Associative Push–Pull Intertwining (`(1 - Q_+)⁻¹ N_+ = N_+ (1 - Q_-)⁻¹`) and
   exact collapse of the Legendre–Schur differential into the Hua–Bergman–Dikin
   Para-Kähler metric `dη_- = (1 - Q_+)⁻¹ dN_+ (1 - Q_-)⁻¹ = (1 - V)⁻¹ dN_+ (1 - V)⁻¹`,
5. Super-LU Bergman Berezinian factorization `(1 - Q_+)(1 - Q_-) = 1 - V` and
   Split-Octonion `ZornMatrix R` DeWitt Sum/Difference realization. -/
theorem para_kahler_super_grassmannian_bruhat_push_pull_dikin_master_poset
    {B : Type*} [Ring B] [Algebra ℚ B] {P : B} (hP : P * P = P)
    (A C dA dC : B)
    (U_plus U_minus U_V : Bˣ)
    (hUp : (U_plus : B) = 1 - qgtPlus P A C)
    (hUm : (U_minus : B) = 1 - qgtMinus P A C)
    (hUV : (U_V : B) = 1 - genV P A C)
    {R : Type*} [Ring R] (x y : Vec3 R) :
    -- (1) Strict acyclicity across 𝔓, 𝔒, and 𝔇
    ((∀ pst : ParaKahlerSuperGrassmannianStage,
        ¬ Relation.TransGen ParaKahlerSuperGrassmannianStage.causalEdge pst pst) ∧
      (∀ ost : SplitOctonionIsotropicAmariStage,
        ¬ Relation.TransGen SplitOctonionIsotropicAmariStage.causalEdge ost ost) ∧
      (∀ dst : AmariDuallyFlatOperatorStage,
        ¬ Relation.TransGen AmariDuallyFlatOperatorStage.causalEdge dst dst)) ∧
    -- (2) Single-chart idempotency vs. naive linear superposition aporia & commutator
    (superGrassmannPrimalChart P A * superGrassmannPrimalChart P A =
        superGrassmannPrimalChart P A ∧
      superGrassmannDualChart P C * superGrassmannDualChart P C =
        superGrassmannDualChart P C ∧
      superGrassmannNaiveSum P A C * superGrassmannNaiveSum P A C -
        superGrassmannNaiveSum P A C = genV P A C ∧
      superGrassmannPrimalChart P A * superGrassmannDualChart P C -
        superGrassmannDualChart P C * superGrassmannPrimalChart P A =
          genSig P A C - genPhi P A C) ∧
    -- (3) Stage 𝔓₃: Bruhat-dressed two-chart idempotent P̂ = P + Φ - Σ - V N_+
    (bruhatDressedProjector P A C =
        P + genPhi P A C - genSig P A C -
          genV P A C * conePlus P A ∧
      bruhatDressedProjector P A C * bruhatDressedProjector P A C =
        bruhatDressedProjector P A C) ∧
    -- (4) Stages 𝔓₄, 𝔓₅: Push-pull intertwiner & Legendre-Schur / Hua-Bergman-Dikin metric
    ((↑U_plus⁻¹ : B) * conePlus P A = conePlus P A * (↑U_minus⁻¹ : B) ∧
      legendreSchurDifferential U_plus P A C dA =
        (↑U_plus⁻¹ : B) * conePlus P dA * (↑U_minus⁻¹ : B) ∧
      huaBergmanDikinMetric U_plus U_minus P dA dC =
        (↑U_V⁻¹ : B) * conePlus P dA * (↑U_V⁻¹ : B) * coneMinus P dC) ∧
    -- (5) Stage 𝔓₆ & Split-Octonion ZornMatrix bridge
    ((1 - qgtPlus P A C) * (1 - qgtMinus P A C) =
        1 - genV P A C ∧
      ZornMatrix.gamma5 * ZornMatrix.zornV x y = ZornMatrix.zornSig x y ∧
      zornMatrixSupertrace (ZornMatrix.zornSig x y) =
        zornMatrixTrace (ZornMatrix.zornV x y)) := by
  have hP12 := rung0_and_stage_P1_P2_unipotent_charts_vs_linear_superposition_aporia hP A 0 C 0
  have hP3 := stage_P3_bruhat_dressed_two_chart_idempotent_cancels_aporia hP A C
  have hP4 :=
    stage_P4_push_pull_intertwiner_and_resolvent_equivariance
      hP A C U_plus U_minus U_V hUp hUm hUV
  have hP5 :=
    stage_P5_legendre_schur_differential_and_hua_bergman_dikin_metric
      hP A C dA dC U_plus U_minus U_V hUp hUm hUV
      (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 isUnit_one
  have hP6 :=
    stage_P6_super_lu_bergman_berezinian_and_split_factorization hP A C (0 : ℤ) 0
  have hO35 :=
    stage_O3_O4_O5_noncommutative_dewitt_sum_metric_and_difference_curvature x y
  exact ⟨⟨ParaKahlerSuperGrassmannianStage.causalEdge_acyclic,
          SplitOctonionIsotropicAmariStage.causalEdge_acyclic,
          AmariDuallyFlatOperatorStage.causalEdge_acyclic⟩,
    ⟨hP12.2.1.2.2.1, hP12.2.1.2.2.2.1, hP12.2.2.1.2.1, hP12.2.2.2.2.2⟩,
    ⟨hP3.2.1.1, hP3.2.2.1.1⟩,
    ⟨hP4.2.1, hP5.2.1.1, hP5.2.2.1.2.1⟩,
    ⟨hP6.2.1.1, hO35.2.1.2, hO35.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset
