/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CattoGurseySplitBasis
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
import InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
Role: Canonical formalization of Stream IX — The Split-Octonion (`𝕆_s`) Circularly
  Polarized Isotropic Witt / Catto–Gürsey Basis, Bi-Lagrangian Metric Split
  (`G_split`), Chiral DeWitt Sum/Difference Separation (`I = u₀ + u₀*` vs.
  `S_P = u₀ - u₀*`), Diquark Hodge Dual (`u_i u_j = ε_{ijk} u_k*`), Amari–Chentsov
  Cubic Baryon Tensor (`T_{ijk} = {u_i u_j, u_k} = ε_{ijk} I`), & Non-Commutative
  Nambu Associator on the DeWitt Difference (`[N_+(u), N_+(u), N_+(u)]_assoc =
  -⟦u⟧ S_P`) (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`):

1. **Rung 0 & Rung 1 (The Socratic Aporia of Isotropic Null Subspaces & Circular
   Polarization from Opposite-Sign Squares)**:
   - Explicit `6 × 6` Bi-Lagrangian split metric matrix `biLagrangianSplitMetric6 =
     [[0₃, I₃], [I₃, 0₃]]`: zero self-blocks on `𝔫₊` and `𝔫₋`, unit cross-block on
     `𝔫₊ × 𝔫₋`, involution `G_split² = I₆`, and non-degenerate split-signature
     determinant `det(G_split) = -1 ≠ 0`.
   - Rung 1 Circular Polarization Theorem: in any noncommutative `[Ring B]`,
     anticommuting compact spin `e² = -1` and hyperbolic boost `ẽ² = +1` (`{e, ẽ} = 0`)
     combine into `U₊ = e + ẽ` and `U₋ = -e + ẽ` with `U₊² = U₋² = 0` (exact isotropic
     nilpotency), `{U₊, U₋} = 4 • 1` (non-degenerate cross-metric), `[U₊, U₋] = 4 • (e * ẽ)`,
     and exact affine unipotent flatness `(1 + U₊)(1 + U₊) = 1 + 2 • U₊`, `(1 + U₊)(1 - U₊) = 1`.
2. **Stages `𝔒₁, 𝔒₂` (Chiral DeWitt Vacuum Idempotents `u₀, u₀*`, Bimodule Polarization,
   Maximal Isotropy of `𝔫₊, 𝔫₋`, & Exact Abelian Ray Exponentials)**:
   - Reuses `InfoGeometry.Canonical.GunaydinGursey` (`signedBasis`, `car_relations`,
     `mixed_table`, `fusion_table`), `InfoGeometry.Superalgebra.PeirceDeWittZornQuantization`
     (`ZornAlgebra`, `e₁`, `e₂`, `quarkU`, `antiquarkV`), and
     `InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset`
     (`ZornMatrix`, `eL`, `eR`, `gamma5`, `psiPlus`, `psiMinus`).
   - Proves bimodule absorption, maximal isotropy `{N_+(x), N_+(y)} = 0`,
     `{N_-(x), N_-(y)} = 0`, `N_+(x)² = 0`, `N_-(y)² = 0`, and exact abelian exponential
     group law `ℰ_+(x₁) ℰ_+(x₂) = ℰ_+(x₁ + x₂)` when `x₁ × x₂ = 0` (in particular along
     every ray `t₁ x, t₂ x`).
3. **Stages `𝔒₃, 𝔒₄, 𝔒₅` (Bi-Lagrangian Cross-Collision onto the Chiral DeWitt Sum
   `I = u₀ + u₀*` as Fisher Metric `V` and DeWitt Difference `S_P = u₀ - u₀*` as Berry
   Curvature `Σ`, plus Chiral Supertrace Recovery)**:
   - Over any noncommutative `[Ring R]` in `ZornMatrix R`:
     `N_+(x) N_-(y) = ⟨x · y, 0, 0, 0⟩`, `N_-(y) N_+(x) = ⟨0, 0, 0, y · x⟩`,
     `V(x, y) = {N_+(x), N_-(y)} = ⟨x · y, 0, 0, y · x⟩`,
     `Σ(x, y) = [N_+(x), N_-(y)] = ⟨x · y, 0, 0, -(y · x)⟩`,
     `γ₅ * V(x, y) = Σ(x, y)`, and `γ₅ * Σ(x, y) = V(x, y)`.
   - Over `[CommRing K]` in `ZornAlgebra K`:
     `{U(x), V(y)} = (x · y) I` and `[U(x), V(y)] = (x · y) S_P`, with
     `trace([U(x), V(y)]) = 0` (Trace-First Blindness) and
     `trace(S_P · [U(x), V(y)]) = trace({U(x), V(y)}) = 2 (x · y)` (Chiral Supertrace
     Recovery).
4. **Stage `𝔒₆` (Split-Octonion Diquark Hodge Dual `N_+(x) N_+(y) = N_-(x × y)` & The
   Amari–Chentsov Cubic Tensor as the 3-Quark Baryon Singlet)**:
   - Proves `N_+(x) N_+(y) = N_-(x × y)` and
     `{N_+(x) N_+(y), N_+(z)} = ⟨z · (x × y), 0, 0, (x × y) · z⟩` over `[Ring R]`,
     which over `[CommRing K]` equals `det(z, x, y) (u₀ + u₀*) = det(x, y, z) I`
     (and on the quadratic moment curve `(1, t, t²)` equals the Vandermonde determinant
     `(t₂ - t₁)(t₃ - t₁)(t₃ - t₂) I`).
5. **Stage `𝔒₇` (Non-Commutative Nambu Associator on the Chiral DeWitt Difference
   `S_P = u₀ - u₀*`)**:
   - Over any noncommutative `[Ring R]` in `ZornMatrix R`, proves
     `(N_+(u) N_+(u)) N_+(u) = ⟨0, 0, 0, ⟦u⟧⟩`,
     `N_+(u) (N_+(u) N_+(u)) = ⟨⟦u⟧, 0, 0, 0⟩`, and
     `[N_+(u), N_+(u), N_+(u)]_assoc = ⟨-⟦u⟧, 0, 0, ⟦u⟧⟩ = -scalarZorn(⟦u⟧) * γ₅`,
     together with a concrete non-vanishing `2 × 2` integer matrix witness.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset

open scoped BigOperators Matrix
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Algebra
open InfoGeometry.Canonical.GunaydinGursey
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization
open InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
open InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset

/-! ===========================================================================
    Section 1: The 7-Stage Split-Octonion Isotropic Circular Amari–Baryon–Nambu
    Causal Poset (`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`)
    =========================================================================== -/

/-- The 7 causal stages of the Split-Octonion (`𝕆_s`) Circularly Polarized
Isotropic Basis, Bi-Lagrangian Metric Split, DeWitt Sum/Difference Separation,
Amari–Chentsov Cubic Baryon Tensor, and Non-Commutative Nambu Associator Poset
(`𝔒₁ ≺ 𝔒₂ ≺ ⋯ ≺ 𝔒₇`). -/
inductive SplitOctonionIsotropicAmariStage : Type
  | O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis
  | O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays
  | O3_BiLagrangianMetricSplitAndCrossVacuumProjection
  | O4_DeWittSumOperatorFisherMetric
  | O5_DeWittDifferenceBerrySkewnessCurvature
  | O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor
  | O7_NonCommutativeNambuAssociatorOnDeWittDifference
  deriving DecidableEq, Repr, Inhabited

namespace SplitOctonionIsotropicAmariStage

/-- Integer rank `0..6` of the 7 split-octonion isotropic Amari stages. -/
def stageIndex : SplitOctonionIsotropicAmariStage → ℕ
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis => 0
  | .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays => 1
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection => 2
  | .O4_DeWittSumOperatorFisherMetric => 3
  | .O5_DeWittDifferenceBerrySkewnessCurvature => 4
  | .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor => 5
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => 6

-- theorem-class: transport lemma
theorem stageIndex_injective : Function.Injective stageIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder SplitOctonionIsotropicAmariStage :=
  LinearOrder.lift' stageIndex stageIndex_injective

instance instFintype : Fintype SplitOctonionIsotropicAmariStage where
  elems := {
    .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis,
    .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays,
    .O3_BiLagrangianMetricSplitAndCrossVacuumProjection,
    .O4_DeWittSumOperatorFisherMetric,
    .O5_DeWittDifferenceBerrySkewnessCurvature,
    .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor,
    .O7_NonCommutativeNambuAssociatorOnDeWittDifference
  }
  complete x := by cases x <;> simp

/-- Directed causal edges `𝔒₁ → 𝔒₂ → 𝔒₃ → (𝔒₄, 𝔒₅) → 𝔒₆ → 𝔒₇`. -/
def causalEdge : SplitOctonionIsotropicAmariStage → SplitOctonionIsotropicAmariStage → Prop
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis,
    .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays => True
  | .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays,
    .O3_BiLagrangianMetricSplitAndCrossVacuumProjection => True
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection,
    .O4_DeWittSumOperatorFisherMetric => True
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection,
    .O5_DeWittDifferenceBerrySkewnessCurvature => True
  | .O4_DeWittSumOperatorFisherMetric,
    .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor => True
  | .O5_DeWittDifferenceBerrySkewnessCurvature,
    .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor => True
  | .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor,
    .O7_NonCommutativeNambuAssociatorOnDeWittDifference => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

-- theorem-class: transport lemma
theorem causalEdge_lt {s t : SplitOctonionIsotropicAmariStage} (h : causalEdge s t) : s < t := by
  change stageIndex s < stageIndex t
  cases s <;> cases t <;> revert h <;> decide

-- theorem-class: transport lemma
theorem transGen_causalEdge_lt {s t : SplitOctonionIsotropicAmariStage}
    (h : Relation.TransGen causalEdge s t) : s < t := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact lt_trans ih (causalEdge_lt h2)

-- theorem-class: transport lemma
theorem causalEdge_acyclic (s : SplitOctonionIsotropicAmariStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact lt_irrefl s (transGen_causalEdge_lt h)

/-- Representation-depth projection `toRepDepth : SplitOctonionIsotropicAmariStage → RepDepth`. -/
def toRepDepth : SplitOctonionIsotropicAmariStage → RepDepth
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis => .projective
  | .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays => .operator
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection => .operator
  | .O4_DeWittSumOperatorFisherMetric => .krein
  | .O5_DeWittDifferenceBerrySkewnessCurvature => .krein
  | .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor => .transport
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => .thermo

-- theorem-class: transport lemma
theorem toRepDepth_rank_monotone {a b : SplitOctonionIsotropicAmariStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

/-- Meta-level projection `toOntologyMetaLevel : SplitOctonionIsotropicAmariStage → OntologyMetaLevel`. -/
def toOntologyMetaLevel : SplitOctonionIsotropicAmariStage → OntologyMetaLevel
  | .O1_ChiralDeWittVacuumIdempotentsAndSumDifferenceBasis => .M1_ProjectorClabject
  | .O2_CircularlyPolarizedIsotropicWittBasesAndAffineRays => .M1_ProjectorClabject
  | .O3_BiLagrangianMetricSplitAndCrossVacuumProjection => .M2_GrassmannianPowertypeOrbit
  | .O4_DeWittSumOperatorFisherMetric => .M2_GrassmannianPowertypeOrbit
  | .O5_DeWittDifferenceBerrySkewnessCurvature => .M2_GrassmannianPowertypeOrbit
  | .O6_SplitOctonionDiquarkHodgeDualAndAmariChentsovCubicBaryonTensor => .M3_ErlangenCasimirMetaLaw
  | .O7_NonCommutativeNambuAssociatorOnDeWittDifference => .M3_ErlangenCasimirMetaLaw

-- theorem-class: transport lemma
theorem toOntologyMetaLevel_rank_monotone {a b : SplitOctonionIsotropicAmariStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change stageIndex a ≤ stageIndex b at h
  cases a <;> cases b <;> revert h <;> decide

end SplitOctonionIsotropicAmariStage

/-! ===========================================================================
    Section 2: Rung 0 & Rung 1 — The Socratic Aporia of Isotropic (Null)
    Subspaces (`G_split = [[0₃, I₃], [I₃, 0₃]]`, `det(G_split) = -1 ≠ 0`)
    and Circular Polarization as the Algebraic Diagonalizer of Nilpotency
    =========================================================================== -/

/-- The `6 × 6` Bi-Lagrangian split metric matrix `G_split = [[0₃, I₃], [I₃, 0₃]]`
of `{ · , · }` in the circularly polarized basis `(u₁, u₂, u₃ ; u₁*, u₂*, u₃*)`. -/
def biLagrangianSplitMetric6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0]

/-- Diagonal grading matrix `S_split6 = diag(I₃, -I₃)` distinguishing the primal
isotropic space `𝔫₊` (`+1`) from the dual isotropic space `𝔫₋` (`-1`). -/
def biLagrangianGrading6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1,  0,  0,  0,  0,  0;
     0,  1,  0,  0,  0,  0;
     0,  0,  1,  0,  0,  0;
     0,  0,  0, -1,  0,  0;
     0,  0,  0,  0, -1,  0;
     0,  0,  0,  0,  0, -1]

-- theorem-class: constructive endpoint
/-- Concrete non-commutativity and chiral anticommutation witness for the `6 × 6`
Bi-Lagrangian split metric matrix `biLagrangianSplitMetric6` and the grading
matrix `biLagrangianGrading6`. -/
theorem biLagrangianSplitMetric6_noncomm_and_anticomm :
    biLagrangianSplitMetric6 * biLagrangianGrading6 ≠
      biLagrangianGrading6 * biLagrangianSplitMetric6 ∧
    biLagrangianSplitMetric6 * biLagrangianGrading6 +
      biLagrangianGrading6 * biLagrangianSplitMetric6 = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h03 := congrFun (congrFun h 0) 3
    revert h03
    decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 200000 in
-- theorem-class: constructive endpoint
/-- **Rung 0 Socratic Aporia Theorem (`rung0_biLagrangian_isotropic_split_metric_nondegenerate`)**:
Refutes the naive Euclidean assumption that vanishing self-metrics on `𝔫₊` (`0..2`)
and `𝔫₋` (`3..5`) force the total metric on `𝔫₊ ⊕ 𝔫₋` to be degenerate:
1. **Zero Primal Self-Block (`g|_{𝔫₊} = 0`)**:
   For all `i, j : Fin 3`, `biLagrangianSplitMetric6 (Fin.castAdd 3 i) (Fin.castAdd 3 j) = 0`.
2. **Zero Dual Self-Block (`g|_{𝔫₋} = 0`)**:
   For all `i, j : Fin 3`, `biLagrangianSplitMetric6 (Fin.natAdd 3 i) (Fin.natAdd 3 j) = 0`.
3. **Kronecker-Delta Cross-Pairing (`g(u_i, u_j*) = δ_{ij}`)**:
   For all `i, j : Fin 3`,
   `biLagrangianSplitMetric6 (Fin.castAdd 3 i) (Fin.natAdd 3 j) = if i = j then 1 else 0`.
4. **Orthogonal Involution (`G_split² = I₆`) & Non-Zero Determinant (`det(G_split) = -1 ≠ 0`)**:
   * `biLagrangianSplitMetric6 * biLagrangianSplitMetric6 = 1`,
   * `Matrix.det biLagrangianSplitMetric6 = -1`,
   * `Matrix.det biLagrangianSplitMetric6 ≠ 0`. -/
theorem rung0_biLagrangian_isotropic_split_metric_nondegenerate :
    (∀ i j : Fin 3, biLagrangianSplitMetric6 (Fin.castAdd 3 i) (Fin.castAdd 3 j) = 0) ∧
    (∀ i j : Fin 3, biLagrangianSplitMetric6 (Fin.natAdd 3 i) (Fin.natAdd 3 j) = 0) ∧
    (∀ i j : Fin 3,
      biLagrangianSplitMetric6 (Fin.castAdd 3 i) (Fin.natAdd 3 j) =
        if i = j then 1 else 0) ∧
    biLagrangianSplitMetric6 * biLagrangianSplitMetric6 =
      (1 : Matrix (Fin 6) (Fin 6) ℤ) ∧
    Matrix.det biLagrangianSplitMetric6 = -1 ∧
    Matrix.det biLagrangianSplitMetric6 ≠ 0 := by
  have hDet : Matrix.det biLagrangianSplitMetric6 = -1 := by decide
  refine ⟨?_, ?_, ?_, ?_, hDet, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · rw [hDet]; decide

section Rung1CircularPolarization

variable {B : Type*} [Ring B]

/-- Unnormalized circularly polarized primal generator `U₊(e, ẽ) := e + ẽ`
combining a compact spin generator `e` (`e² = -1`) and a hyperbolic boost
generator `ẽ` (`ẽ² = +1`). -/
def circularPolarizedPlus (e eTilde : B) : B :=
  e + eTilde

/-- Unnormalized circularly polarized dual generator `U₋(e, ẽ) := -e + ẽ`. -/
def circularPolarizedMinus (e eTilde : B) : B :=
  -e + eTilde

-- theorem-class: constructive endpoint
/-- **Rung 1 Circular Polarization Theorem
(`rung1_circular_polarization_nilpotency_from_opposite_squares`)**:
In any noncommutative `[Ring B]`, let `e` be a compact spin axis (`e * e = -1`)
and `eTilde` a hyperbolic boost axis (`eTilde * eTilde = 1`) that anticommute
(`e * eTilde + eTilde * e = 0`):
1. **Exact Isotropic Nilpotency (`U₊² = 0` and `U₋² = 0`)**:
   * `circularPolarizedPlus e eTilde * circularPolarizedPlus e eTilde = 0`,
   * `circularPolarizedMinus e eTilde * circularPolarizedMinus e eTilde = 0`.
2. **Non-Degenerate Cross-Pairing on the Identity & Chiral Commutator**:
   * `circularPolarizedPlus e eTilde * circularPolarizedMinus e eTilde +
      circularPolarizedMinus e eTilde * circularPolarizedPlus e eTilde = (4 : ℤ) • (1 : B)`,
   * `circularPolarizedPlus e eTilde * circularPolarizedMinus e eTilde -
      circularPolarizedMinus e eTilde * circularPolarizedPlus e eTilde = (4 : ℤ) • (e * eTilde)`.
3. **Exact Affine Exponential Flatness & Series-Free Inversion**:
   * `(1 + circularPolarizedPlus e eTilde) * (1 + circularPolarizedPlus e eTilde) =
      1 + (2 : ℤ) • circularPolarizedPlus e eTilde`,
   * `(1 + circularPolarizedPlus e eTilde) * (1 - circularPolarizedPlus e eTilde) = 1`,
   * `(1 + circularPolarizedMinus e eTilde) * (1 - circularPolarizedMinus e eTilde) = 1`. -/
theorem rung1_circular_polarization_nilpotency_from_opposite_squares
    {e eTilde : B} (he : e * e = -1) (heT : eTilde * eTilde = 1)
    (hAnti : e * eTilde + eTilde * e = 0) :
    let U_plus := circularPolarizedPlus e eTilde
    let U_minus := circularPolarizedMinus e eTilde
    (U_plus * U_plus = 0 ∧
      U_minus * U_minus = 0) ∧
    (U_plus * U_minus + U_minus * U_plus = (4 : ℤ) • (1 : B) ∧
      U_plus * U_minus - U_minus * U_plus = (4 : ℤ) • (e * eTilde)) ∧
    ((1 + U_plus) * (1 + U_plus) = 1 + (2 : ℤ) • U_plus ∧
      (1 + U_plus) * (1 - U_plus) = 1 ∧
      (1 + U_minus) * (1 - U_minus) = 1) := by
  intro U_plus U_minus
  have hAntiSwap : eTilde * e = -(e * eTilde) := eq_neg_of_add_eq_zero_right hAnti
  have hUpSq : U_plus * U_plus = 0 := by
    dsimp [U_plus, circularPolarizedPlus]
    calc
      (e + eTilde) * (e + eTilde)
        = e * e + (e * eTilde + eTilde * e) + eTilde * eTilde := by noncomm_ring
      _ = -1 + 0 + 1 := by rw [he, hAnti, heT]
      _ = 0 := by abel
  have hUmSq : U_minus * U_minus = 0 := by
    dsimp [U_minus, circularPolarizedMinus]
    calc
      (-e + eTilde) * (-e + eTilde)
        = e * e - (e * eTilde + eTilde * e) + eTilde * eTilde := by noncomm_ring
      _ = -1 - 0 + 1 := by rw [he, hAnti, heT]
      _ = 0 := by abel
  have hCrossSum : U_plus * U_minus + U_minus * U_plus = (4 : ℤ) • (1 : B) := by
    dsimp [U_plus, U_minus, circularPolarizedPlus, circularPolarizedMinus]
    calc
      (e + eTilde) * (-e + eTilde) + (-e + eTilde) * (e + eTilde)
        = (2 : ℤ) • (eTilde * eTilde) - (2 : ℤ) • (e * e) := by noncomm_ring
      _ = (2 : ℤ) • (1 : B) - (2 : ℤ) • (-1 : B) := by rw [heT, he]
      _ = (4 : ℤ) • (1 : B) := by abel
  have hCrossDiff : U_plus * U_minus - U_minus * U_plus = (4 : ℤ) • (e * eTilde) := by
    dsimp [U_plus, U_minus, circularPolarizedPlus, circularPolarizedMinus]
    calc
      (e + eTilde) * (-e + eTilde) - (-e + eTilde) * (e + eTilde)
        = (2 : ℤ) • (e * eTilde) - (2 : ℤ) • (eTilde * e) := by noncomm_ring
      _ = (2 : ℤ) • (e * eTilde) - (2 : ℤ) • (-(e * eTilde)) := by rw [hAntiSwap]
      _ = (4 : ℤ) • (e * eTilde) := by abel
  have hAffUp : (1 + U_plus) * (1 + U_plus) = 1 + (2 : ℤ) • U_plus := by
    calc
      (1 + U_plus) * (1 + U_plus)
        = 1 + (2 : ℤ) • U_plus + U_plus * U_plus := by noncomm_ring
      _ = 1 + (2 : ℤ) • U_plus := by rw [hUpSq, add_zero]
  have hInvUp : (1 + U_plus) * (1 - U_plus) = 1 := by
    calc
      (1 + U_plus) * (1 - U_plus) = 1 - U_plus * U_plus := by noncomm_ring
      _ = 1 := by rw [hUpSq, sub_zero]
  have hInvUm : (1 + U_minus) * (1 - U_minus) = 1 := by
    calc
      (1 + U_minus) * (1 - U_minus) = 1 - U_minus * U_minus := by noncomm_ring
      _ = 1 := by rw [hUmSq, sub_zero]
  exact ⟨⟨hUpSq, hUmSq⟩, ⟨hCrossSum, hCrossDiff⟩, ⟨hAffUp, hInvUp, hInvUm⟩⟩

end Rung1CircularPolarization

/-! ===========================================================================
    Section 3: Stages `𝔒₁, 𝔒₂` — Chiral DeWitt Vacuum Idempotents (`u₀, u₀*`),
    Bimodule Polarization, Maximal Isotropy of `𝔫₊, 𝔫₋`, & Abelian Ray
    Exponentials in `ZornAlgebra K` and `ZornVectorMatrix K`
    =========================================================================== -/

section StagesO1O2IsotropicSubspacesAndAffineExponentials

variable {K : Type*} [CommRing K]

/-- The Chiral DeWitt Difference `S_P = u₀ - u₀* = e₁ - e₂ = [[1, 0], [0, -1]]`
in `ZornAlgebra K`. -/
def zornDeWittDiff : ZornAlgebra K :=
  ZornAlgebra.sub ZornAlgebra.e₁ ZornAlgebra.e₂

/-- The primal `e`-flat isotropic exponential map `ℰ₊(x) := I + U(x)` in `ZornAlgebra K`. -/
def zornExpPlus (x : ColorVec3 K) : ZornAlgebra K :=
  ZornAlgebra.add ZornAlgebra.one (ZornAlgebra.quarkU x)

/-- The dual `m`-flat isotropic exponential map `ℰ₋(y) := I + V(y)` in `ZornAlgebra K`. -/
def zornExpMinus (y : ColorVec3 K) : ZornAlgebra K :=
  ZornAlgebra.add ZornAlgebra.one (ZornAlgebra.antiquarkV y)

-- theorem-class: constructive endpoint
/-- **Stages `𝔒₁, 𝔒₂` Theorem
(`stage_O1_O2_dewitt_vacuum_bimodule_isotropy_and_ray_exponentials`)**:
Over any commutative ring `K` in `ZornAlgebra K` (and via `signedBasis` in
`ZornVectorMatrix K`):
1. **Stage `𝔒₁` (Chiral DeWitt Vacuum Idempotents & Sum/Difference Basis)**:
   * `e₁ · e₁ = e₁`, `e₂ · e₂ = e₂`, `e₁ · e₂ = 0`, `e₂ · e₁ = 0`,
   * `e₁ + e₂ = I` (DeWitt Sum) and `S_P = e₁ - e₂` satisfies `S_P · S_P = I`,
   * In `ZornVectorMatrix K`, `(uZero : ZornVectorMatrix K) + uStarZero = one` and
     `mul (uZero - uStarZero) (uZero - uStarZero) = one`.
2. **Stage `𝔒₂` (Chiral Bimodule Absorption & Maximal Isotropy of `𝔫₊` and `𝔫₋`)**:
   * `e₁ · U(x) = U(x) = U(x) · e₂` and `e₂ · U(x) = 0 = U(x) · e₁`,
   * `e₂ · V(y) = V(y) = V(y) · e₁` and `e₁ · V(y) = 0 = V(y) · e₂`,
   * `{U(x), U(y)} = 0` and `{V(x), V(y)} = 0` for ALL `x, y : ColorVec3 K`
     (maximal isotropy of the 3D subspaces `𝔫₊` and `𝔫₋`!),
   * `U(x) · U(x) = 0` and `V(y) · V(y) = 0`,
   * In `ZornVectorMatrix K`, `mul (u i) (u j) + mul (u j) (u i) = 0` and
     `mul (uStar i) (uStar j) + mul (uStar j) (uStar i) = 0` for all `i, j : Fin 3`.
3. **Exact Ray Exponential Group Law & Series-Free Inversion (`ℰ₊, ℰ₋`)**:
   * Along any color direction `x`, `ℰ₊(t₁ • x) · ℰ₊(t₂ • x) = ℰ₊((t₁ + t₂) • x)`,
   * Along any dual color direction `y`, `ℰ₋(t₁ • y) · ℰ₋(t₂ • y) = ℰ₋((t₁ + t₂) • y)`,
   * `ℰ₊(x) · ℰ₊(-x) = I` and `ℰ₋(y) · ℰ₋(-y) = I`. -/
theorem stage_O1_O2_dewitt_vacuum_bimodule_isotropy_and_ray_exponentials
    (x y : ColorVec3 K) (t₁ t₂ : K) (i j : Fin 3) :
    -- (1) Stage 𝔒₁: Chiral DeWitt Vacuum Idempotents & Sum/Difference
    (ZornAlgebra.mul (ZornAlgebra.e₁ : ZornAlgebra K) ZornAlgebra.e₁ = ZornAlgebra.e₁ ∧
      ZornAlgebra.mul (ZornAlgebra.e₂ : ZornAlgebra K) ZornAlgebra.e₂ = ZornAlgebra.e₂ ∧
      ZornAlgebra.mul (ZornAlgebra.e₁ : ZornAlgebra K) ZornAlgebra.e₂ = ZornAlgebra.zero ∧
      ZornAlgebra.mul (ZornAlgebra.e₂ : ZornAlgebra K) ZornAlgebra.e₁ = ZornAlgebra.zero ∧
      ZornAlgebra.add (ZornAlgebra.e₁ : ZornAlgebra K) ZornAlgebra.e₂ = ZornAlgebra.one ∧
      ZornAlgebra.mul (zornDeWittDiff : ZornAlgebra K) zornDeWittDiff = ZornAlgebra.one ∧
      (uZero : ZornVectorMatrix K) + uStarZero = ZornVectorMatrix.one ∧
      ZornVectorMatrix.mul (uZero - uStarZero : ZornVectorMatrix K) (uZero - uStarZero) =
        ZornVectorMatrix.one) ∧
    -- (2) Stage 𝔒₂: Bimodule Polarization & Maximal Isotropy of 𝔫₊ and 𝔫₋
    (ZornAlgebra.mul ZornAlgebra.e₁ (ZornAlgebra.quarkU x) = ZornAlgebra.quarkU x ∧
      ZornAlgebra.mul (ZornAlgebra.quarkU x) ZornAlgebra.e₂ = ZornAlgebra.quarkU x ∧
      ZornAlgebra.mul ZornAlgebra.e₂ (ZornAlgebra.quarkU x) = ZornAlgebra.zero ∧
      ZornAlgebra.mul (ZornAlgebra.quarkU x) ZornAlgebra.e₁ = ZornAlgebra.zero ∧
      ZornAlgebra.mul ZornAlgebra.e₂ (ZornAlgebra.antiquarkV y) = ZornAlgebra.antiquarkV y ∧
      ZornAlgebra.mul (ZornAlgebra.antiquarkV y) ZornAlgebra.e₁ = ZornAlgebra.antiquarkV y ∧
      ZornAlgebra.anticommutator (ZornAlgebra.quarkU x) (ZornAlgebra.quarkU y) =
        ZornAlgebra.zero ∧
      ZornAlgebra.anticommutator (ZornAlgebra.antiquarkV x) (ZornAlgebra.antiquarkV y) =
        ZornAlgebra.zero ∧
      ZornAlgebra.mul (ZornAlgebra.quarkU x) (ZornAlgebra.quarkU x) = ZornAlgebra.zero ∧
      ZornAlgebra.mul (ZornAlgebra.antiquarkV y) (ZornAlgebra.antiquarkV y) = ZornAlgebra.zero ∧
      ZornVectorMatrix.mul (u i : ZornVectorMatrix K) (u j) +
        ZornVectorMatrix.mul (u j) (u i) = 0 ∧
      ZornVectorMatrix.mul (uStar i : ZornVectorMatrix K) (uStar j) +
        ZornVectorMatrix.mul (uStar j) (uStar i) = 0) ∧
    -- (3) Exact Ray Exponential Group Law & Series-Free Inversion
    (ZornAlgebra.mul (zornExpPlus (ColorVec3.smul t₁ x)) (zornExpPlus (ColorVec3.smul t₂ x)) =
        zornExpPlus (ColorVec3.smul (t₁ + t₂) x) ∧
      ZornAlgebra.mul (zornExpMinus (ColorVec3.smul t₁ y)) (zornExpMinus (ColorVec3.smul t₂ y)) =
        zornExpMinus (ColorVec3.smul (t₁ + t₂) y) ∧
      ZornAlgebra.mul (zornExpPlus x) (zornExpPlus (ColorVec3.neg x)) = ZornAlgebra.one ∧
      ZornAlgebra.mul (zornExpMinus y) (zornExpMinus (ColorVec3.neg y)) = ZornAlgebra.one) := by
  have hCAR := car_relations (R := K) i j
  refine ⟨⟨ZornAlgebra.e₁_idempotent, ZornAlgebra.e₂_idempotent,
           ZornAlgebra.e₁_mul_e₂_zero, ZornAlgebra.e₂_mul_e₁_zero,
           ZornAlgebra.peirce_partition_of_unity,
           by ext <;> dsimp [zornDeWittDiff, ZornAlgebra.sub, ZornAlgebra.mul,
                ZornAlgebra.e₁, ZornAlgebra.e₂, ZornAlgebra.one,
                ColorVec3.zero, ColorVec3.sub, ColorVec3.add, ColorVec3.smul,
                ColorVec3.dot, ColorVec3.cross] <;> ring,
           singlet_sum (R := K),
           grading_square (R := K)⟩,
    ⟨ZornAlgebra.e₁_mul_quarkU x, ZornAlgebra.quarkU_mul_e₂ x,
     ZornAlgebra.e₂_mul_quarkU x, ZornAlgebra.quarkU_mul_e₁ x,
     ZornAlgebra.e₂_mul_antiquarkV y, ZornAlgebra.antiquarkV_mul_e₁ y,
     by ext <;> dsimp [ZornAlgebra.anticommutator, ZornAlgebra.add, ZornAlgebra.mul,
          ZornAlgebra.quarkU, ZornAlgebra.zero, ColorVec3.zero, ColorVec3.add,
          ColorVec3.sub, ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [ZornAlgebra.anticommutator, ZornAlgebra.add, ZornAlgebra.mul,
          ZornAlgebra.antiquarkV, ZornAlgebra.zero, ColorVec3.zero, ColorVec3.add,
          ColorVec3.sub, ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     ZornAlgebra.quarkU_sq_zero x,
     ZornAlgebra.antiquarkV_sq_zero y,
     hCAR.1,
     hCAR.2.1⟩,
    ⟨by ext <;> dsimp [zornExpPlus, ZornAlgebra.add, ZornAlgebra.mul, ZornAlgebra.one,
          ZornAlgebra.quarkU, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
          ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [zornExpMinus, ZornAlgebra.add, ZornAlgebra.mul, ZornAlgebra.one,
          ZornAlgebra.antiquarkV, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
          ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [zornExpPlus, ZornAlgebra.add, ZornAlgebra.mul, ZornAlgebra.one,
          ZornAlgebra.quarkU, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
          ColorVec3.neg, ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [zornExpMinus, ZornAlgebra.add, ZornAlgebra.mul, ZornAlgebra.one,
          ZornAlgebra.antiquarkV, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
          ColorVec3.neg, ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring⟩⟩

end StagesO1O2IsotropicSubspacesAndAffineExponentials

/-! ===========================================================================
    Section 4: Stages `𝔒₃, 𝔒₄, 𝔒₅` — Bi-Lagrangian Cross-Collision onto the
    Chiral DeWitt Sum (`I = u₀ + u₀*`) as Operator Fisher Metric `V` and the
    Chiral DeWitt Difference (`S_P = u₀ - u₀*`) as Berry Curvature `Σ`,
    Plus Trace-First Blindness vs. Chiral Supertrace Recovery
    =========================================================================== -/

section StagesO3O4O5DeWittSumMetricAndDifferenceCurvature

variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- Ungraded trace `Tr(X) = X.a + X.d` on `ZornMatrix R`. -/
def zornMatrixTrace (X : ZornMatrix R) : R :=
  X.a + X.d

/-- Chiral supertrace `Str(X) = Tr(γ₅ * X) = X.a - X.d` on `ZornMatrix R`. -/
def zornMatrixSupertrace (X : ZornMatrix R) : R :=
  (ZornMatrix.gamma5 * X).a + (ZornMatrix.gamma5 * X).d

open ZornMatrix in
-- theorem-class: constructive endpoint
/-- **Stages `𝔒₃, 𝔒₄, 𝔒₅` Non-Commutative Theorem
(`stage_O3_O4_O5_noncommutative_dewitt_sum_metric_and_difference_curvature`)**:
Over ANY noncommutative `[Ring R]` in `ZornMatrix R`, for `N_+(x) = psiPlus x`
and `N_-(y) = psiMinus y`:
1. **Stage `𝔒₃` (Directed Vacuum Projections onto `u₀ = e_L` and `u₀* = e_R`)**:
   * `psiPlus x * psiMinus y = ⟨Vec3.dot x y, 0, 0, 0⟩` (`(x · y) u₀`),
   * `psiMinus y * psiPlus x = ⟨0, 0, 0, Vec3.dot y x⟩` (`(y · x) u₀*`).
2. **Stage `𝔒₄` (DeWitt Sum = Operator Fisher Metric `V(x, y) = {N_+(x), N_-(y)}`)**:
   * `ZornMatrix.zornV x y = ⟨Vec3.dot x y, 0, 0, Vec3.dot y x⟩`,
   * `ZornMatrix.gamma5 * ZornMatrix.zornV x y = ZornMatrix.zornSig x y`.
3. **Stage `𝔒₅` (DeWitt Difference = Berry Curvature `Σ(x, y) = [N_+(x), N_-(y)]`)**:
   * `ZornMatrix.zornSig x y = ⟨Vec3.dot x y, 0, 0, -Vec3.dot y x⟩`,
   * `ZornMatrix.gamma5 * ZornMatrix.zornSig x y = ZornMatrix.zornV x y`,
   * **Chiral Supertrace Recovery**:
     `zornMatrixSupertrace (ZornMatrix.zornSig x y) = zornMatrixTrace (ZornMatrix.zornV x y)` and
     `zornMatrixSupertrace (ZornMatrix.zornV x y) = zornMatrixTrace (ZornMatrix.zornSig x y)`. -/
theorem stage_O3_O4_O5_noncommutative_dewitt_sum_metric_and_difference_curvature
    (x y : Vec3 R) :
    (ZornMatrix.psiPlus x * ZornMatrix.psiMinus y = ⟨Vec3.dot x y, 0, 0, 0⟩ ∧
      ZornMatrix.psiMinus y * ZornMatrix.psiPlus x = ⟨0, 0, 0, Vec3.dot y x⟩) ∧
    (ZornMatrix.zornV x y = ⟨Vec3.dot x y, 0, 0, Vec3.dot y x⟩ ∧
      ZornMatrix.gamma5 * ZornMatrix.zornV x y = ZornMatrix.zornSig x y) ∧
    (ZornMatrix.zornSig x y = ⟨Vec3.dot x y, 0, 0, -Vec3.dot y x⟩ ∧
      ZornMatrix.gamma5 * ZornMatrix.zornSig x y = ZornMatrix.zornV x y ∧
      zornMatrixSupertrace (ZornMatrix.zornSig x y) =
        zornMatrixTrace (ZornMatrix.zornV x y) ∧
      zornMatrixSupertrace (ZornMatrix.zornV x y) =
        zornMatrixTrace (ZornMatrix.zornSig x y)) := by
  refine ⟨⟨by zorn_ring, by zorn_ring⟩,
    ⟨by zorn_ring, by zorn_ring⟩,
    ⟨by zorn_ring, by zorn_ring,
     by dsimp [zornMatrixSupertrace, zornMatrixTrace]; zorn_ring,
     by dsimp [zornMatrixSupertrace, zornMatrixTrace]; zorn_ring⟩⟩

-- theorem-class: constructive endpoint
/-- **Stages `𝔒₃, 𝔒₄, 𝔒₅` Commutative-Base Theorem
(`stage_O3_O4_O5_commutative_dewitt_sum_and_difference_separation`)**:
Over any commutative ring `K` in `ZornAlgebra K`:
1. **Cross-Products Land on `(u₀, u₀*) = (e₁, e₂)`**:
   * `U(x) · V(y) = (x · y) e₁`,
   * `V(y) · U(x) = (x · y) e₂`.
2. **DeWitt Sum = Operator Fisher Metric `V`**:
   * `{U(x), V(y)} = (x · y) (e₁ + e₂) = (x · y) I`.
3. **DeWitt Difference = Berry / Amari Skewness Tensor `Σ`**:
   * `[U(x), V(y)] = (x · y) (e₁ - e₂) = (x · y) S_P`.
4. **Textbook Trace-First Blindness vs. Chiral Supertrace Recovery**:
   * `ZornAlgebra.trace ([U(x), V(y)]) = 0` (ordinary trace is blind to `Σ`!),
   * `ZornAlgebra.trace (S_P · [U(x), V(y)]) = ZornAlgebra.trace ({U(x), V(y)}) = 2 (x · y)`. -/
theorem stage_O3_O4_O5_commutative_dewitt_sum_and_difference_separation
    (x y : ColorVec3 K) :
    (ZornAlgebra.mul (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y) =
        ZornAlgebra.smul (ColorVec3.dot x y) ZornAlgebra.e₁ ∧
      ZornAlgebra.mul (ZornAlgebra.antiquarkV y) (ZornAlgebra.quarkU x) =
        ZornAlgebra.smul (ColorVec3.dot x y) ZornAlgebra.e₂) ∧
    ZornAlgebra.anticommutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y) =
      ZornAlgebra.smul (ColorVec3.dot x y) ZornAlgebra.one ∧
    ZornAlgebra.commutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y) =
      ZornAlgebra.smul (ColorVec3.dot x y) zornDeWittDiff ∧
    (ZornAlgebra.trace (ZornAlgebra.commutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y)) = 0 ∧
      ZornAlgebra.trace
          (ZornAlgebra.mul zornDeWittDiff
            (ZornAlgebra.commutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y))) =
        ZornAlgebra.trace
          (ZornAlgebra.anticommutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y)) ∧
      ZornAlgebra.trace
          (ZornAlgebra.mul zornDeWittDiff
            (ZornAlgebra.commutator (ZornAlgebra.quarkU x) (ZornAlgebra.antiquarkV y))) =
        ColorVec3.dot x y + ColorVec3.dot x y) := by
  refine ⟨⟨?_, ?_⟩, ZornAlgebra.zorn_car_quantization_exact x y, ?_, ⟨?_, ?_, ?_⟩⟩
  · ext <;> dsimp [ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
      ZornAlgebra.smul, ZornAlgebra.e₁, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring
  · ext <;> dsimp [ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
      ZornAlgebra.smul, ZornAlgebra.e₂, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring
  · ext <;> dsimp [ZornAlgebra.commutator, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.quarkU, ZornAlgebra.antiquarkV, ZornAlgebra.smul, zornDeWittDiff,
      ZornAlgebra.e₁, ZornAlgebra.e₂, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
      ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring
  · dsimp [ZornAlgebra.trace, ZornAlgebra.commutator, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.quarkU, ZornAlgebra.antiquarkV, ColorVec3.dot]
    ring
  · dsimp [ZornAlgebra.trace, zornDeWittDiff, ZornAlgebra.commutator,
      ZornAlgebra.anticommutator, ZornAlgebra.add, ZornAlgebra.sub, ZornAlgebra.mul,
      ZornAlgebra.e₁, ZornAlgebra.e₂, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
      ColorVec3.zero, ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.dot,
      ColorVec3.cross]
    ring
  · dsimp [ZornAlgebra.trace, zornDeWittDiff, ZornAlgebra.commutator,
      ZornAlgebra.sub, ZornAlgebra.mul, ZornAlgebra.e₁, ZornAlgebra.e₂,
      ZornAlgebra.quarkU, ZornAlgebra.antiquarkV, ColorVec3.zero, ColorVec3.add,
      ColorVec3.sub, ColorVec3.smul, ColorVec3.dot, ColorVec3.cross]
    ring

end StagesO3O4O5DeWittSumMetricAndDifferenceCurvature

/-! ===========================================================================
    Section 5: Stage `𝔒₆` — Split-Octonion Diquark Hodge Dual
    (`N_+(x) N_+(y) = N_-(x × y) ∈ 𝔫₋`) & The Amari–Chentsov Cubic Tensor as
    the 3-Quark Baryon Singlet (`{N_+(x) N_+(y), N_+(z)} = det(x, y, z) I`)
    =========================================================================== -/

section StageO6DiquarkDualAndAmariChentsovCubicBaryonTensor

variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- The Non-Commutative Amari–Chentsov Cubic Baryon Tensor
`amariChentsovBaryonNC x y z := {N_+(x) N_+(y), N_+(z)}` in `ZornMatrix R`. -/
def amariChentsovBaryonNC (x y z : Vec3 R) : ZornMatrix R :=
  ZornMatrix.anticommZorn (ZornMatrix.psiPlus x * ZornMatrix.psiPlus y) (ZornMatrix.psiPlus z)

/-- The Commutative-Base Amari–Chentsov Cubic Baryon Tensor
`amariChentsovBaryon x y z := {U(x) · U(y), U(z)}` in `ZornAlgebra K`. -/
def amariChentsovBaryon (x y z : ColorVec3 K) : ZornAlgebra K :=
  ZornAlgebra.anticommutator
    (ZornAlgebra.mul (ZornAlgebra.quarkU x) (ZornAlgebra.quarkU y))
    (ZornAlgebra.quarkU z)

open ZornMatrix in
-- theorem-class: constructive endpoint
/-- **Stage `𝔒₆` Theorem
(`stage_O6_diquark_hodge_dual_and_amari_chentsov_cubic_baryon_tensor`)**:
1. **Non-Commutative Diquark Hodge Dual & Cubic Tensor over `[Ring R]` (`ZornMatrix R`)**:
   * `psiPlus x * psiPlus y = psiMinus (Vec3.cross x y)` (maps `𝔫₊ × 𝔫₊ → 𝔫₋`),
   * `psiMinus x * psiMinus y = psiPlus (-Vec3.cross x y)` (maps `𝔫₋ × 𝔫₋ → 𝔫₊`),
   * `amariChentsovBaryonNC x y z =
        ZornMatrix.anticommZorn (ZornMatrix.psiMinus (Vec3.cross x y)) (ZornMatrix.psiPlus z)`,
   * `amariChentsovBaryonNC x y z =
        ⟨Vec3.dot z (Vec3.cross x y), 0, 0, Vec3.dot (Vec3.cross x y) z⟩`.
2. **Commutative-Base Amari–Chentsov Cubic Baryon Singlet over `[CommRing K]` (`ZornAlgebra K`)**:
   * `U(x) · U(y) = V(x × y)` and `[U(x), U(y)] = 2 V(x × y)` (since `{U(x), U(y)} = 0`),
   * `amariChentsovBaryon x y z = det(z, x, y) I = det(x, y, z) (e₁ + e₂)`,
   * Orthonormal RGB basis normalization:
     `amariChentsovBaryon ColorVec3.e_r ColorVec3.e_g ColorVec3.e_b = ZornAlgebra.one`,
   * On the quadratic moment curve `colorMomentCurve t = (1, t, t²)`,
     `amariChentsovBaryon (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
        ((t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂)) I` (the Vandermonde determinant!). -/
theorem stage_O6_diquark_hodge_dual_and_amari_chentsov_cubic_baryon_tensor
    (x y z : Vec3 R) (xk yk zk : ColorVec3 K) (t₁ t₂ t₃ : K) :
    -- (1) Non-commutative diquark dual & cubic tensor in `ZornMatrix R`
    (ZornMatrix.psiPlus x * ZornMatrix.psiPlus y = ZornMatrix.psiMinus (Vec3.cross x y) ∧
      ZornMatrix.psiMinus x * ZornMatrix.psiMinus y = ZornMatrix.psiPlus (-Vec3.cross x y) ∧
      amariChentsovBaryonNC x y z =
        ZornMatrix.anticommZorn (ZornMatrix.psiMinus (Vec3.cross x y)) (ZornMatrix.psiPlus z) ∧
      amariChentsovBaryonNC x y z =
        ⟨Vec3.dot z (Vec3.cross x y), 0, 0, Vec3.dot (Vec3.cross x y) z⟩) ∧
    -- (2) Commutative-base cubic baryon singlet & Vandermonde moment curve in `ZornAlgebra K`
    (ZornAlgebra.mul (ZornAlgebra.quarkU xk) (ZornAlgebra.quarkU yk) =
        ZornAlgebra.antiquarkV (ColorVec3.cross xk yk) ∧
      ZornAlgebra.commutator (ZornAlgebra.quarkU xk) (ZornAlgebra.quarkU yk) =
        ZornAlgebra.add
          (ZornAlgebra.antiquarkV (ColorVec3.cross xk yk))
          (ZornAlgebra.antiquarkV (ColorVec3.cross xk yk)) ∧
      amariChentsovBaryon xk yk zk =
        ZornAlgebra.smul (ColorVec3.baryonDet xk yk zk) ZornAlgebra.one ∧
      amariChentsovBaryon (ColorVec3.e_r : ColorVec3 K) ColorVec3.e_g ColorVec3.e_b =
        ZornAlgebra.one ∧
      amariChentsovBaryon (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
        ZornAlgebra.smul ((t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂)) ZornAlgebra.one) := by
  have hDiquarkNC :
      ZornMatrix.psiPlus x * ZornMatrix.psiPlus y = ZornMatrix.psiMinus (Vec3.cross x y) := by
    zorn_ring
  refine ⟨⟨hDiquarkNC,
           by zorn_ring,
           by unfold amariChentsovBaryonNC; rw [hDiquarkNC],
           by dsimp [amariChentsovBaryonNC]; zorn_ring⟩,
    ⟨ZornAlgebra.supercolor_diquark_fusion xk yk,
     by ext <;> dsimp [ZornAlgebra.commutator, ZornAlgebra.sub, ZornAlgebra.add,
          ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.antiquarkV,
          ColorVec3.zero, ColorVec3.add, ColorVec3.sub, ColorVec3.smul,
          ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [amariChentsovBaryon, ZornAlgebra.anticommutator, ZornAlgebra.add,
          ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.smul, ZornAlgebra.one,
          ColorVec3.baryonDet, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
          ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring,
     by ext <;> dsimp [amariChentsovBaryon, ZornAlgebra.anticommutator, ZornAlgebra.add,
          ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.one,
          ColorVec3.e_r, ColorVec3.e_g, ColorVec3.e_b, ColorVec3.zero,
          ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.dot,
          ColorVec3.cross] <;> ring,
     by
       have hCub :
           amariChentsovBaryon (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
             ZornAlgebra.smul
               (ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃))
               ZornAlgebra.one := by
         ext <;> dsimp [amariChentsovBaryon, ZornAlgebra.anticommutator, ZornAlgebra.add,
           ZornAlgebra.mul, ZornAlgebra.quarkU, ZornAlgebra.smul, ZornAlgebra.one,
           ColorVec3.baryonDet, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
           ColorVec3.smul, ColorVec3.dot, ColorVec3.cross] <;> ring
       rw [hCub, baryonDet_colorMomentCurve_eq_vandermonde_product]⟩⟩

end StageO6DiquarkDualAndAmariChentsovCubicBaryonTensor

/-! ===========================================================================
    Section 6: Stage `𝔒₇` — Non-Commutative Nambu Associator on the Chiral
    DeWitt Difference `S_P = u₀ - u₀* = γ₅` & Concrete `2 × 2` Matrix Witness
    =========================================================================== -/

section StageO7NonCommutativeNambuAssociator

variable {R : Type*} [Ring R]

/-- Diagonal scalar embedding `scalarZorn s := ⟨s, 0, 0, s⟩ = s (u₀ + u₀*)`
in `ZornMatrix R`. -/
def scalarZorn (s : R) : ZornMatrix R :=
  ⟨s, 0, 0, s⟩

open ZornMatrix in
-- theorem-class: constructive endpoint
/-- **Stage `𝔒₇` Theorem (`stage_O7_noncommutative_nambu_associator_on_dewitt_difference`)**:
Over ANY noncommutative `[Ring R]` in `ZornMatrix R`:
1. **Chromomagnetic Self-Wedge (`N_+(u)² = N_-(u × u)`)**:
   * `ZornMatrix.psiPlus u * ZornMatrix.psiPlus u = ZornMatrix.psiMinus (Vec3.cross u u)`,
   * `ZornMatrix.psiMinus v * ZornMatrix.psiMinus v = ZornMatrix.psiPlus (-Vec3.cross v v)`.
2. **Opposite-Vacuum Parenthesizations of the Cube (`(N_+²) N_+` vs. `N_+ (N_+²)`)**:
   * `(ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u =
        ⟨0, 0, 0, Vec3.nambu3 u⟩` (`⟦u⟧ u₀*`),
   * `ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) =
        ⟨Vec3.nambu3 u, 0, 0, 0⟩` (`⟦u⟧ u₀`).
3. **Symmetric Sum Lands on the DeWitt Sum `I = u₀ + u₀*`**:
   `((ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u) +
     (ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u)) =
       scalarZorn (Vec3.nambu3 u)`.
4. **Non-Commutative Nambu Associator Lands Strictly on the DeWitt Difference
   `S_P = u₀ - u₀* = γ₅`**:
   * `ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
        ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩`,
   * `ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
        -(scalarZorn (Vec3.nambu3 u) * ZornMatrix.gamma5)`,
   * `ZornMatrix.cubicAssociator (ZornMatrix.psiMinus v) =
        -(scalarZorn (Vec3.nambu3 v) * ZornMatrix.gamma5)`. -/
theorem stage_O7_noncommutative_nambu_associator_on_dewitt_difference
    (u v : Vec3 R) :
    (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u =
        ZornMatrix.psiMinus (Vec3.cross u u) ∧
      ZornMatrix.psiMinus v * ZornMatrix.psiMinus v =
        ZornMatrix.psiPlus (-Vec3.cross v v)) ∧
    ((ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u =
        ⟨0, 0, 0, Vec3.nambu3 u⟩ ∧
      ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) =
        ⟨Vec3.nambu3 u, 0, 0, 0⟩) ∧
    (((ZornMatrix.psiPlus u * ZornMatrix.psiPlus u) * ZornMatrix.psiPlus u) +
        (ZornMatrix.psiPlus u * (ZornMatrix.psiPlus u * ZornMatrix.psiPlus u)) =
      scalarZorn (Vec3.nambu3 u)) ∧
    (ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
        ⟨-Vec3.nambu3 u, 0, 0, Vec3.nambu3 u⟩ ∧
      ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
        -(scalarZorn (Vec3.nambu3 u) * ZornMatrix.gamma5) ∧
      ZornMatrix.cubicAssociator (ZornMatrix.psiMinus v) =
        -(scalarZorn (Vec3.nambu3 v) * ZornMatrix.gamma5)) := by
  refine ⟨⟨by zorn_ring, by zorn_ring⟩,
    ⟨by zorn_ring, by zorn_ring⟩,
    by dsimp [scalarZorn]; zorn_ring,
    ⟨by zorn_ring,
     by dsimp [scalarZorn]; zorn_ring,
     by dsimp [scalarZorn]; zorn_ring⟩⟩

end StageO7NonCommutativeNambuAssociator

/-- Concrete `2 × 2` integer matrix vector `u_mat = (E₀₁, E₁₀, diag(1, -1))`
whose non-commutative Nambu 3-bracket `⟦u_mat⟧ = u_mat · (u_mat × u_mat)` is non-zero. -/
def nambuWitnessVec3 : Vec3 (Matrix (Fin 2) (Fin 2) ℤ) where
  x := !![0, 1; 0, 0]
  y := !![0, 0; 1, 0]
  z := !![1, 0; 0, -1]

-- theorem-class: constructive endpoint
/-- Concrete non-commutative witness over `R = Matrix (Fin 2) (Fin 2) ℤ`:
`Vec3.nambu3 nambuWitnessVec3 ≠ 0` and
`ZornMatrix.cubicAssociator (ZornMatrix.psiPlus nambuWitnessVec3) ≠ 0`. -/
theorem nambuWitnessVec3_associator_ne_zero :
    Vec3.nambu3 nambuWitnessVec3 ≠ 0 ∧
    ZornMatrix.cubicAssociator (ZornMatrix.psiPlus nambuWitnessVec3) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    revert h00
    decide
  · intro h
    have ha := congrArg ZornMatrix.a h
    have h00 := congrFun (congrFun ha 0) 0
    revert h00
    decide

/-! ===========================================================================
    Section 7: Zorn Composition, Lagrange Correction, and Alternativity
    (`𝔃₁ ≺ ⋯ ≺ 𝔃₆`)
    =========================================================================== -/

/-- Stages for the coordinate-level Zorn composition identities.  This order
records dependencies; it does not classify all products satisfying them. -/
inductive ZornCompositionStage : Type
  | Z1_PeirceCarrier
  | Z2_LagrangeCrossCorrection
  | Z3_NormComposition
  | Z4_AdjugateAndQuadraticIdentity
  | Z5_Alternativity
  | Z6_FlexibleLaw
  deriving DecidableEq, Repr, Inhabited

namespace ZornCompositionStage

/-- Rank of the six Zorn composition stages. -/
def rank : ZornCompositionStage → ℕ
  | .Z1_PeirceCarrier => 0
  | .Z2_LagrangeCrossCorrection => 1
  | .Z3_NormComposition => 2
  | .Z4_AdjugateAndQuadraticIdentity => 3
  | .Z5_Alternativity => 4
  | .Z6_FlexibleLaw => 5

/-- Consecutive dependency edges for the Zorn composition stages. -/
def causalEdge : ZornCompositionStage → ZornCompositionStage → Prop
  | .Z1_PeirceCarrier, .Z2_LagrangeCrossCorrection => True
  | .Z2_LagrangeCrossCorrection, .Z3_NormComposition => True
  | .Z3_NormComposition, .Z4_AdjugateAndQuadraticIdentity => True
  | .Z4_AdjugateAndQuadraticIdentity, .Z5_Alternativity => True
  | .Z5_Alternativity, .Z6_FlexibleLaw => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {s t : ZornCompositionStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {s t : ZornCompositionStage}
    (h : Relation.TransGen causalEdge s t) : rank s < rank t := by
  induction h with
  | single hst => exact causalEdge_rank_lt hst
  | tail _ hst ih => exact Nat.lt_trans ih (causalEdge_rank_lt hst)

theorem causalEdge_acyclic (s : ZornCompositionStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl _ (transGen_causalEdge_rank_lt h)

end ZornCompositionStage

section ZornComposition

variable {K : Type*} [CommRing K]

/-- Zorn's quadratic determinant on the repository's `ZornMatrix` carrier. -/
def zornMatrixDet (X : ZornMatrix K) : K :=
  X.a * X.d - Vec3.dot X.u X.v

/-- The adjugate of a Zorn vector-matrix. -/
def zornMatrixAdj (X : ZornMatrix K) : ZornMatrix K :=
  ⟨X.d, -X.u, -X.v, X.a⟩

/-- Scalar diagonal embedding used in the Zorn adjugate and quadratic identity. -/
def zornMatrixScalar (r : K) : ZornMatrix K :=
  ⟨r, 0, 0, r⟩

/-- Purely `[propext]`-based commutative ring normalizer (expands products, canonicalizes
multiplicative monomials via `mul_assoc, mul_comm, mul_left_comm`, and cancels additive terms
without invoking `Quot.sound`). -/
macro "comm_ring_propext" : tactic =>
  `(tactic| (
    simp only [sub_eq_add_neg, mul_add, add_mul, neg_add_rev, neg_neg,
      neg_mul, mul_neg, zero_add, add_zero, one_mul, mul_one, zero_mul, mul_zero, neg_zero]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    abel))

/-- Four-vector Lagrange–Binet–Cauchy identity for the repository's `Vec3` cross
product. -/
theorem zornVec3_lagrange (a b c d : Vec3 K) :
    Vec3.dot (Vec3.cross a b) (Vec3.cross c d) =
      Vec3.dot a c * Vec3.dot b d - Vec3.dot a d * Vec3.dot b c := by
  dsimp [Vec3.dot, Vec3.cross]
  comm_ring_propext

/-- Zorn norm composition on the same `ZornMatrix K` carrier used by the
split-octonion isotropic stages. -/
theorem zornMatrixDet_mul (X Y : ZornMatrix K) :
    zornMatrixDet (X * Y) = zornMatrixDet X * zornMatrixDet Y := by
  simp [zornMatrixDet, ZornMatrix.mul, Vec3.dot, Vec3.cross,
    Vec3.smulLeft, Vec3.smulRight]
  ring

/-- Both orders of multiplication by the Zorn adjugate give the determinant
times the scalar diagonal element. -/
theorem zornMatrix_mul_adj (X : ZornMatrix K) :
    X * zornMatrixAdj X = zornMatrixScalar (zornMatrixDet X) ∧
      zornMatrixAdj X * X = zornMatrixScalar (zornMatrixDet X) := by
  constructor <;> ext <;>
    simp [zornMatrixAdj, zornMatrixScalar, zornMatrixDet,
      ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- Cayley–Hamilton identity for Zorn matrices, with trace `a + d` and
determinant `a*d - u·v`. -/
theorem zornMatrix_cayley_hamilton (X : ZornMatrix K) :
    X * X - zornMatrixScalar (zornMatrixTrace X) * X +
      zornMatrixScalar (zornMatrixDet X) = 0 := by
  ext <;> simp [zornMatrixTrace, zornMatrixDet, zornMatrixScalar,
    ZornMatrix.mul, Vec3.dot, Vec3.cross,
    Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- Left alternativity of `ZornMatrix K`: `(X*X)*Y = X*(X*Y)`. -/
theorem zornMatrix_left_alternative (X Y : ZornMatrix K) :
    (X * X) * Y = X * (X * Y) := by
  ext <;> simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
    Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- Right alternativity of `ZornMatrix K`: `(Y*X)*X = Y*(X*X)`. -/
theorem zornMatrix_right_alternative (X Y : ZornMatrix K) :
    (Y * X) * X = Y * (X * X) := by
  ext <;> simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
    Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- Flexibility of `ZornMatrix K`: `(X*Y)*X = X*(Y*X)`. -/
theorem zornMatrix_flexible (X Y : ZornMatrix K) :
    (X * Y) * X = X * (Y * X) := by
  ext <;> simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
    Vec3.smulLeft, Vec3.smulRight] <;> ring

/-- Naive `2 × 2` block multiplication on `ZornMatrix K` omitting the 3D Hodge cross-product
couplings `-X.v × Y.v` and `+X.u × Y.u`. -/
def zornMulNaive (X Y : ZornMatrix K) : ZornMatrix K :=
  ⟨X.a * Y.a + Vec3.dot X.u Y.v,
   Vec3.smulLeft X.a Y.u + Vec3.smulRight X.u Y.d,
   Vec3.smulLeft Y.a X.v + Vec3.smulRight Y.v X.d,
   Vec3.dot X.v Y.u + X.d * Y.d⟩

/-- First unit reflection Zorn matrix `X₁ = ⟨0, e₁, e₁, 0⟩`. -/
def zornReflE1 : ZornMatrix K :=
  ⟨0, ⟨1, 0, 0⟩, ⟨1, 0, 0⟩, 0⟩

/-- Second orthogonal unit reflection Zorn matrix `X₂ = ⟨0, e₂, e₂, 0⟩`. -/
def zornReflE2 : ZornMatrix K :=
  ⟨0, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩, 0⟩

/-- Chiral `e₃`-axis rotation Zorn matrix `⟨0, -e₃, e₃, 0⟩ = X₁ * X₂`. -/
def zornReflE3Rot : ZornMatrix K :=
  ⟨0, ⟨0, 0, -1⟩, ⟨0, 0, 1⟩, 0⟩

-- theorem-class: constructive endpoint
/-- **Stages `𝔃₁, 𝔃₂` Theorem
(`z1_z2_orthogonal_reflection_naive_collapse_vs_zorn_volume_preservation`)**:
1. **Exact Cross-Product Difference Between Zorn and Naive Block Multiplication**:
   `X * Y - zornMulNaive X Y = ⟨0, -Vec3.cross X.v Y.v, Vec3.cross X.u Y.u, 0⟩`.
2. **Orthogonal Unit Reflections (`zornReflE1`, `zornReflE2`)**:
   * `zornMatrixDet zornReflE1 = -1` and `zornMatrixDet zornReflE2 = -1`,
   * `zornReflE1 * zornReflE1 = 1` and `zornReflE2 * zornReflE2 = 1`.
3. **Naive Block Multiplication Collapse Aporia**:
   * `zornMulNaive zornReflE1 zornReflE2 = 0`,
   * `zornMatrixDet (zornMulNaive zornReflE1 zornReflE2) = 0`.
4. **Zorn Cross-Product Repair & Volume Preservation**:
   * `zornReflE1 * zornReflE2 = zornReflE3Rot`,
   * `zornMatrixDet (zornReflE1 * zornReflE2) = 1`,
   * `zornMatrixDet (zornReflE1 * zornReflE2) =
        zornMatrixDet zornReflE1 * zornMatrixDet zornReflE2`. -/
theorem z1_z2_orthogonal_reflection_naive_collapse_vs_zorn_volume_preservation
    (X Y : ZornMatrix K) :
    (X * Y - zornMulNaive X Y = ⟨0, -Vec3.cross X.v Y.v, Vec3.cross X.u Y.u, 0⟩) ∧
    (zornMatrixDet (zornReflE1 : ZornMatrix K) = -1 ∧
      zornMatrixDet (zornReflE2 : ZornMatrix K) = -1 ∧
      (zornReflE1 : ZornMatrix K) * zornReflE1 = 1 ∧
      (zornReflE2 : ZornMatrix K) * zornReflE2 = 1) ∧
    (zornMulNaive (zornReflE1 : ZornMatrix K) zornReflE2 = 0 ∧
      zornMatrixDet (zornMulNaive (zornReflE1 : ZornMatrix K) zornReflE2) = 0) ∧
    ((zornReflE1 : ZornMatrix K) * zornReflE2 = zornReflE3Rot ∧
      zornMatrixDet ((zornReflE1 : ZornMatrix K) * zornReflE2) = 1 ∧
      zornMatrixDet ((zornReflE1 : ZornMatrix K) * zornReflE2) =
        zornMatrixDet (zornReflE1 : ZornMatrix K) *
          zornMatrixDet (zornReflE2 : ZornMatrix K)) := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · ext <;> simp [zornMulNaive, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · simp [zornMatrixDet, zornReflE1, Vec3.dot]
  · simp [zornMatrixDet, zornReflE2, Vec3.dot]
  · ext <;> simp [zornReflE1, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornReflE2, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornMulNaive, zornReflE1, zornReflE2, Vec3.dot,
      Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMatrixDet, zornMulNaive, zornReflE1, zornReflE2, Vec3.dot,
      Vec3.smulLeft, Vec3.smulRight]
  · ext <;> simp [zornReflE1, zornReflE2, zornReflE3Rot, ZornMatrix.mul,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMatrixDet, zornReflE1, zornReflE2, ZornMatrix.mul,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [zornMatrixDet, zornReflE1, zornReflE2, ZornMatrix.mul,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]

-- theorem-class: structural API
/-- **Stages `𝔃₃, 𝔃₄` Binet–Cauchy / Lagrange Cross-Term Repair Identity**:
The naive dot-product term `(u₁ · v₂)(v₁ · u₂)` minus the Zorn cross-product dot pairing
`(-v₁ × v₂) · (u₁ × u₂)` recovers the exact factorized product `(u₁ · v₁)(u₂ · v₂)`. -/
theorem zornVec3_binet_cauchy_lagrange_repair (u₁ v₁ u₂ v₂ : Vec3 K) :
    Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂ -
      Vec3.dot (-Vec3.cross v₁ v₂) (Vec3.cross u₁ u₂) =
      Vec3.dot u₁ v₁ * Vec3.dot u₂ v₂ := by
  dsimp [Vec3.dot, Vec3.cross]
  change (u₁.x * v₂.x + u₁.y * v₂.y + u₁.z * v₂.z) * (v₁.x * u₂.x + v₁.y * u₂.y + v₁.z * u₂.z) -
    (-(v₁.y * v₂.z - v₁.z * v₂.y) * (u₁.y * u₂.z - u₁.z * u₂.y) +
     -(v₁.z * v₂.x - v₁.x * v₂.z) * (u₁.z * u₂.x - u₁.x * u₂.z) +
     -(v₁.x * v₂.y - v₁.y * v₂.x) * (u₁.x * u₂.y - u₁.y * u₂.x)) =
    (u₁.x * v₁.x + u₁.y * v₁.y + u₁.z * v₁.z) * (u₂.x * v₂.x + u₂.y * v₂.y + u₂.z * v₂.z)
  comm_ring_propext

-- theorem-class: structural API
/-- **Stage `𝔃₅` BAC–CAB Vector Triple Product & Longitudinal Cancellation**:
1. `v × (u × w) = (v · w) u - (v · u) w`,
2. `(v · w) u - v × (u × w) = (u · v) w`. -/
theorem zornVec3_bac_cab_longitudinal (u v w : Vec3 K) :
    Vec3.cross v (Vec3.cross u w) =
      Vec3.smulLeft (Vec3.dot v w) u - Vec3.smulLeft (Vec3.dot v u) w ∧
    Vec3.smulLeft (Vec3.dot v w) u - Vec3.cross v (Vec3.cross u w) =
      Vec3.smulLeft (Vec3.dot u v) w := by
  constructor <;> ext <;> simp [Vec3.cross, Vec3.dot, Vec3.smulLeft] <;> comm_ring_propext

-- theorem-class: constructive endpoint
/-- Left Moufang identity in `ZornMatrix K`: `(X * (Y * X)) * Z = X * (Y * (X * Z))`. -/
theorem zornMatrix_left_moufang (X Y Z : ZornMatrix K) :
    (X * (Y * X)) * Z = X * (Y * (X * Z)) := by
  ext <;>
    simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring

-- theorem-class: constructive endpoint
/-- Right Moufang identity in `ZornMatrix K`: `Z * (X * (Y * X)) = ((Z * X) * Y) * X`. -/
theorem zornMatrix_right_moufang (X Y Z : ZornMatrix K) :
    Z * (X * (Y * X)) = ((Z * X) * Y) * X := by
  ext <;>
    simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring

-- theorem-class: constructive endpoint
/-- Middle Moufang identity in `ZornMatrix K`: `(X * Y) * (Z * X) = X * ((Y * Z) * X)`. -/
theorem zornMatrix_middle_moufang (X Y Z : ZornMatrix K) :
    (X * Y) * (Z * X) = X * ((Y * Z) * X) := by
  ext <;>
    simp [ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring

-- theorem-class: capstone consumer theorem
/-- **Complete 6-Stage `[propext]`-Only Zorn Composition, Binet–Cauchy, Cayley–Hamilton,
& BAC–CAB / Moufang Alternativity Closure (`𝔃₁ ≺ ⋯ ≺ 𝔃₆`)**:
Bundles all six stages of `ZornCompositionStage` into a single constructive theorem over
any commutative ring `[CommRing K]`. -/
theorem zorn_composition_binet_cauchy_cayley_hamilton_moufang_closure
    (X Y Z : ZornMatrix K) (u v w : Vec3 K) :
    -- (1) Poset acyclicity of 𝔃₁ ≺ ⋯ ≺ 𝔃₆
    (∀ st : ZornCompositionStage,
      ¬ Relation.TransGen ZornCompositionStage.causalEdge st st) ∧
    -- (2) Stages 𝔃₁, 𝔃₂: Naive reflection collapse vs. Zorn volume preservation
    (zornMulNaive (zornReflE1 : ZornMatrix K) zornReflE2 = 0 ∧
      (zornReflE1 : ZornMatrix K) * zornReflE2 = zornReflE3Rot ∧
      zornMatrixDet ((zornReflE1 : ZornMatrix K) * zornReflE2) =
        zornMatrixDet (zornReflE1 : ZornMatrix K) *
          zornMatrixDet (zornReflE2 : ZornMatrix K)) ∧
    -- (3) Stages 𝔃₃, 𝔃₄: Binet–Cauchy repair, 8D norm multiplicativity, adjugate & Cayley–Hamilton
    (Vec3.dot X.u Y.v * Vec3.dot X.v Y.u -
        Vec3.dot (-Vec3.cross X.v Y.v) (Vec3.cross X.u Y.u) =
        Vec3.dot X.u X.v * Vec3.dot Y.u Y.v ∧
      zornMatrixDet (X * Y) = zornMatrixDet X * zornMatrixDet Y ∧
      X * zornMatrixAdj X = zornMatrixScalar (zornMatrixDet X) ∧
      zornMatrixAdj X * X = zornMatrixScalar (zornMatrixDet X) ∧
      X * X - zornMatrixScalar (zornMatrixTrace X) * X +
        zornMatrixScalar (zornMatrixDet X) = 0) ∧
    -- (4) Stages 𝔃₅, 𝔃₆: BAC–CAB, Left/Right/Flexible Alternativity, and 3 Moufang Identities
    (Vec3.smulLeft (Vec3.dot v w) u - Vec3.cross v (Vec3.cross u w) =
        Vec3.smulLeft (Vec3.dot u v) w ∧
      (X * X) * Y = X * (X * Y) ∧
      (Y * X) * X = Y * (X * X) ∧
      (X * Y) * X = X * (Y * X) ∧
      (X * (Y * X)) * Z = X * (Y * (X * Z)) ∧
      Z * (X * (Y * X)) = ((Z * X) * Y) * X ∧
      (X * Y) * (Z * X) = X * ((Y * Z) * X)) := by
  have hZ12 := z1_z2_orthogonal_reflection_naive_collapse_vs_zorn_volume_preservation X Y
  have hAdj := zornMatrix_mul_adj X
  exact ⟨ZornCompositionStage.causalEdge_acyclic,
    ⟨hZ12.2.2.1.1, hZ12.2.2.2.1, hZ12.2.2.2.2.2⟩,
    ⟨zornVec3_binet_cauchy_lagrange_repair X.u X.v Y.u Y.v,
     zornMatrixDet_mul X Y,
     hAdj.1,
     hAdj.2,
     zornMatrix_cayley_hamilton X⟩,
    ⟨(zornVec3_bac_cab_longitudinal u v w).2,
     zornMatrix_left_alternative X Y,
     zornMatrix_right_alternative X Y,
     zornMatrix_flexible X Y,
     zornMatrix_left_moufang X Y Z,
     zornMatrix_right_moufang X Y Z,
     zornMatrix_middle_moufang X Y Z⟩⟩

end ZornComposition

/-! ===========================================================================
    Section 7b: The 6-Stage Metriplectic Zorn Three-Channel Product,
    Three-Term Pythagorean Norm Law, & Third-Order Baryon/Associator Volume
    Duality Poset (`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ ⋯ ≺ 𝔐ℨ₆`)
    =========================================================================== -/

/-- The 6 stages of the **Metriplectic Zorn Three-Channel Product & Volume Duality Poset**
(`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`). -/
inductive MetriplecticZornStage : Type
  /-- `𝔐ℨ₁`: DeWitt Basis `(1, I_para)` & Three-Channel Projection Operators (`g`, `ω`, `×_H`). -/
  | MZ1_DeWittBasisAndThreeChannelProjectors
  /-- `𝔐ℨ₂`: Exact Three-Term Metriplectic Zorn Decomposition `2 z₁ z₂ = g 1 + ω I_para + 2(z₁ ×_H z₂)`. -/
  | MZ2_ThreeTermMetriplecticZornDecomposition
  /-- `𝔐ℨ₃`: Para-Kähler Locking `ω(z₁, z₂) = g(I_para z₁, z₂)` & Jordan–Malcev Tangent Split. -/
  | MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit
  /-- `𝔐ℨ₄`: Three-Term Metriplectic Pythagorean Determinant Law `4 det(z₁ z₂) = g² - ω² - 4 det(z₁ ×_H z₂)`. -/
  | MZ4_ThreeTermMetriplecticPythagoreanNormLaw
  /-- `𝔐ℨ₅`: 3rd-Order Dual Volume Split on `1` (Baryon Cubic) vs. `I_para` (Associator). -/
  | MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator
  /-- `𝔐ℨ₆`: Non-Commutative Nambu Associator Specialization `[N_+(u), N_+(u), N_+(u)]_assoc = -⟦u⟧ I_para`. -/
  | MZ6_NonCommutativeNambuAssociatorSpecialization
  deriving DecidableEq, Repr, Inhabited

namespace MetriplecticZornStage

/-- Topological rank `0 .. 5` of the 6 Metriplectic Zorn stages. -/
def rank : MetriplecticZornStage → ℕ
  | .MZ1_DeWittBasisAndThreeChannelProjectors => 0
  | .MZ2_ThreeTermMetriplecticZornDecomposition => 1
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => 2
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw => 3
  | .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator => 4
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder MetriplecticZornStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype MetriplecticZornStage where
  elems := {
    .MZ1_DeWittBasisAndThreeChannelProjectors,
    .MZ2_ThreeTermMetriplecticZornDecomposition,
    .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit,
    .MZ4_ThreeTermMetriplecticPythagoreanNormLaw,
    .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator,
    .MZ6_NonCommutativeNambuAssociatorSpecialization
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MetriplecticZornStage = 6 := rfl

/-- Directed diamond causal edges `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`. -/
def causalEdge : MetriplecticZornStage → MetriplecticZornStage → Prop
  | .MZ1_DeWittBasisAndThreeChannelProjectors,
    .MZ2_ThreeTermMetriplecticZornDecomposition => True
  | .MZ2_ThreeTermMetriplecticZornDecomposition,
    .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => True
  | .MZ2_ThreeTermMetriplecticZornDecomposition,
    .MZ4_ThreeTermMetriplecticPythagoreanNormLaw => True
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit,
    .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator => True
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw,
    .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator => True
  | .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator,
    .MZ6_NonCommutativeNambuAssociatorSpecialization => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : MetriplecticZornStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : MetriplecticZornStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- **DAG Acyclicity Theorem (`MetriplecticZornStage.causalEdge_acyclic`)**:
No stage in `𝔐ℨ₁..𝔐ℨ₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (s : MetriplecticZornStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl _ (transGen_causalEdge_rank_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : MetriplecticZornStage → RepDepth
  | .MZ1_DeWittBasisAndThreeChannelProjectors => .operator
  | .MZ2_ThreeTermMetriplecticZornDecomposition => .operator
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => .transport
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw => .transport
  | .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator => .thermo
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => .thermo

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : MetriplecticZornStage → OntologyMetaLevel
  | .MZ1_DeWittBasisAndThreeChannelProjectors => .M1_ProjectorClabject
  | .MZ2_ThreeTermMetriplecticZornDecomposition => .M1_ProjectorClabject
  | .MZ3_ParaKahlerLockingAndJordanMalcevTangentSplit => .M2_GrassmannianPowertypeOrbit
  | .MZ4_ThreeTermMetriplecticPythagoreanNormLaw => .M2_GrassmannianPowertypeOrbit
  | .MZ5_ThirdOrderDualVolumeSplitBaryonVsAssociator => .M3_ErlangenCasimirMetaLaw
  | .MZ6_NonCommutativeNambuAssociatorSpecialization => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_monotone {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> unfold toRepDepth RepDepth.toNat <;> decide

theorem toOntologyMetaLevel_monotone {a b : MetriplecticZornStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> unfold toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end MetriplecticZornStage

section MetriplecticZornThreeChannelClosure

variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- Tangent space embedding `zornTangent u v := ⟨0, u, v, 0⟩ ∈ 𝔫₊ ⊕ 𝔫₋` inside `ZornMatrix R`. -/
def zornTangent (u v : Vec3 R) : ZornMatrix R :=
  ⟨0, u, v, 0⟩

/-- Diagonal projection `zornDiagPart X := ⟨X.a, 0, 0, X.d⟩` onto `𝔨 = R 1 ⊕ R I_para`. -/
def zornDiagPart (X : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a, 0, 0, X.d⟩

/-- Chiral DeWitt Difference `zornIPara := ⟨1, 0, 0, -1⟩ = u₀ - u₀* = γ₅` in `ZornMatrix R`. -/
def zornIPara : ZornMatrix R :=
  ZornMatrix.gamma5

/-- Channel 1 (DeWitt Sum Fisher / Onsager Metric):
`zornFisherMetric z₁ z₂ := tr_Zorn(z₁ z₂) = (a₁ a₂ + d₁ d₂) + (u₁ · v₂ + v₁ · u₂)`. -/
def zornFisherMetric (z₁ z₂ : ZornMatrix R) : R :=
  (z₁.a * z₂.a + z₁.d * z₂.d) + (Vec3.dot z₁.u z₂.v + Vec3.dot z₁.v z₂.u)

/-- Channel 2 (DeWitt Difference Symplectic / Berry 2-Form):
`zornSymplecticForm z₁ z₂ := tr_Zorn(I_para z₁ z₂) = (a₁ a₂ - d₁ d₂) + (u₁ · v₂ - v₁ · u₂)`. -/
def zornSymplecticForm (z₁ z₂ : ZornMatrix R) : R :=
  (z₁.a * z₂.a - z₁.d * z₂.d) + (Vec3.dot z₁.u z₂.v - Vec3.dot z₁.v z₂.u)

/-- Channel 3 (Off-Diagonal Hodge Diquark Cross Product `z₁ ×_H z₂ ∈ 𝔫₊ ⊕ 𝔫₋`):
`⟨0, a₁ u₂ + u₁ d₂ - v₁ × v₂, v₁ a₂ + d₁ v₂ + u₁ × u₂, 0⟩`. -/
def zornHodgeCross (z₁ z₂ : ZornMatrix R) : ZornMatrix R :=
  ⟨0,
   Vec3.smulLeft z₁.a z₂.u + Vec3.smulRight z₁.u z₂.d - Vec3.cross z₁.v z₂.v,
   Vec3.smulRight z₁.v z₂.a + Vec3.smulLeft z₁.d z₂.v + Vec3.cross z₁.u z₂.u,
   0⟩

/-- 3D Baryon / Scalar Triple Product `zornVec3Det u₁ u₂ u₃ := (u₁ × u₂) · u₃`. -/
def zornVec3Det (u₁ u₂ u₃ : Vec3 R) : R :=
  Vec3.dot (Vec3.cross u₁ u₂) u₃

/-- Associator `[X, Y, Z]_assoc := (X * Y) * Z - X * (Y * Z)` on `ZornMatrix R`. -/
def zornAssoc (X Y Z : ZornMatrix R) : ZornMatrix R :=
  (X * Y) * Z - X * (Y * Z)

-- theorem-class: constructive endpoint
/-- **Stages `𝔐ℨ₁, 𝔐ℨ₂, 𝔐ℨ₃` Theorem
(`stage_MZ1_MZ2_MZ3_metriplectic_three_channel_decomposition_and_jordan_malcev_split`)**:
1. **Stage `𝔐ℨ₁` (DeWitt Basis & Trace Projections over `[Ring R]`)**:
   * `zornIPara * zornIPara = (1 : ZornMatrix R)`,
   * `zornMatrixTrace (z₁ * z₂) = zornFisherMetric z₁ z₂`,
   * `zornMatrixTrace (zornIPara * (z₁ * z₂)) = zornSymplecticForm z₁ z₂`,
   * **Para-Kähler Locking**: `zornFisherMetric (zornIPara * z₁) z₂ = zornSymplecticForm z₁ z₂`.
2. **Stage `𝔐ℨ₂` (Exact Three-Term Metriplectic Zorn Decomposition over `[Ring R]`)**:
   `z₁ * z₂ + z₁ * z₂ =
     scalarZorn (zornFisherMetric z₁ z₂) +
       scalarZorn (zornSymplecticForm z₁ z₂) * zornIPara +
       (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂)`.
3. **Stage `𝔐ℨ₃` (Jordan–Malcev Tangent Split on `𝔭 = 𝔫₊ ⊕ 𝔫₋` over `[CommRing K]`)**:
   For `t₁ = zornTangent u₁ v₁` and `t₂ = zornTangent u₂ v₂`:
   * `zornFisherMetric t₁ t₂ = zornFisherMetric t₂ t₁` (symmetric Fisher metric),
   * `zornSymplecticForm t₁ t₂ = -zornSymplecticForm t₂ t₁` (skew-symmetric symplectic form),
   * `zornHodgeCross t₁ t₂ = -zornHodgeCross t₂ t₁` (skew-symmetric Hodge cross product),
   * **Jordan Anticommutator**: `t₁ * t₂ + t₂ * t₁ = zornMatrixScalar (zornFisherMetric t₁ t₂)`,
   * **Malcev Commutator**:
     `t₁ * t₂ - t₂ * t₁ =
       zornMatrixScalar (zornSymplecticForm t₁ t₂) * zornIPara +
         (zornHodgeCross t₁ t₂ + zornHodgeCross t₁ t₂)`. -/
theorem stage_MZ1_MZ2_MZ3_metriplectic_three_channel_decomposition_and_jordan_malcev_split
    (z₁ z₂ : ZornMatrix R) (u₁ v₁ u₂ v₂ : Vec3 K) :
    let t₁ := zornTangent u₁ v₁
    let t₂ := zornTangent u₂ v₂
    -- (1) Stage 𝔐ℨ₁: DeWitt basis, trace readouts & Para-Kähler locking
    ((zornIPara : ZornMatrix R) * zornIPara = 1 ∧
      zornMatrixTrace (z₁ * z₂) = zornFisherMetric z₁ z₂ ∧
      zornMatrixTrace (zornIPara * (z₁ * z₂)) = zornSymplecticForm z₁ z₂ ∧
      zornFisherMetric (zornIPara * z₁) z₂ = zornSymplecticForm z₁ z₂) ∧
    -- (2) Stage 𝔐ℨ₂: Exact Three-Term Metriplectic Zorn Decomposition
    (z₁ * z₂ + z₁ * z₂ =
      scalarZorn (zornFisherMetric z₁ z₂) +
        scalarZorn (zornSymplecticForm z₁ z₂) * zornIPara +
        (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂)) ∧
    -- (3) Stage 𝔐ℨ₃: Jordan-Malcev tangent split on 𝔭
    (zornFisherMetric t₁ t₂ = zornFisherMetric t₂ t₁ ∧
      zornSymplecticForm t₁ t₂ = -zornSymplecticForm t₂ t₁ ∧
      zornHodgeCross t₁ t₂ = -zornHodgeCross t₂ t₁ ∧
      t₁ * t₂ + t₂ * t₁ = zornMatrixScalar (zornFisherMetric t₁ t₂) ∧
      t₁ * t₂ - t₂ * t₁ =
        zornMatrixScalar (zornSymplecticForm t₁ t₂) * zornIPara +
          (zornHodgeCross t₁ t₂ + zornHodgeCross t₁ t₂)) := by
  intro t₁ t₂
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [zornIPara]; zorn_ring
  · dsimp [zornMatrixTrace, zornFisherMetric, ZornMatrix.mul, Vec3.dot]; abel
  · dsimp [zornMatrixTrace, zornSymplecticForm, zornIPara, ZornMatrix.gamma5, ZornMatrix.mul]
    vec3_ring
  · dsimp [zornFisherMetric, zornSymplecticForm, zornIPara, ZornMatrix.gamma5, ZornMatrix.mul]
    vec3_ring
  · dsimp [scalarZorn, zornFisherMetric, zornSymplecticForm, zornIPara, zornHodgeCross]
    zorn_ring
  · dsimp [t₁, t₂, zornTangent, zornFisherMetric, Vec3.dot]; ring
  · dsimp [t₁, t₂, zornTangent, zornSymplecticForm, Vec3.dot]; ring
  · ext <;> simp [t₁, t₂, zornTangent, zornHodgeCross, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [t₁, t₂, zornTangent, zornMatrixScalar, zornFisherMetric,
      ZornMatrix.mul, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [t₁, t₂, zornTangent, zornMatrixScalar, zornSymplecticForm,
      zornIPara, ZornMatrix.gamma5, zornHodgeCross, ZornMatrix.mul,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring

-- theorem-class: constructive endpoint
/-- **Stage `𝔐ℨ₄` Theorem (`stage_MZ4_three_term_metriplectic_pythagorean_norm_law`)**:
For tangent elements `z₁ = zornTangent u₁ v₁` and `z₂ = zornTangent u₂ v₂` in `ZornMatrix K`:
1. **Rung 0 Socratic Aporia of the Two-Term Para-Kähler Modulus**:
   * `zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
        zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ =
          4 * (Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂)`,
   * On orthogonal unit reflections `zornReflE1` and `zornReflE2`, both `g` and `ω` vanish
     (`zornFisherMetric zornReflE1 zornReflE2 = 0`, `zornSymplecticForm zornReflE1 zornReflE2 = 0`),
     whereas the 3rd channel `zornHodgeCross zornReflE1 zornReflE2 = zornReflE3Rot` carries the
     entire volume (`zornMatrixDet (zornHodgeCross zornReflE1 zornReflE2) = 1`).
2. **Off-Diagonal Hodge Cross-Product Determinant**:
   `zornMatrixDet (zornHodgeCross z₁ z₂) = Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂)`
   (since `zornMatrixDet ⟨0, -v₁ × v₂, u₁ × u₂, 0⟩ = 0 - (-v₁ × v₂) · (u₁ × u₂)`).
3. **Exact Three-Term Metriplectic Pythagorean Determinant Law**:
   * `4 * zornMatrixDet (z₁ * z₂) =
        zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
          zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ +
          4 * zornMatrixDet (zornHodgeCross z₁ z₂)`,
   * `zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
        zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ +
        4 * zornMatrixDet (zornHodgeCross z₁ z₂) =
          4 * (zornMatrixDet z₁ * zornMatrixDet z₂)`. -/
theorem stage_MZ4_three_term_metriplectic_pythagorean_norm_law
    (u₁ v₁ u₂ v₂ : Vec3 K) :
    let z₁ := zornTangent u₁ v₁
    let z₂ := zornTangent u₂ v₂
    -- (1) Rung 0 two-term modulus & orthogonal reflection aporia witness
    (zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
        zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ =
        4 * (Vec3.dot u₁ v₂ * Vec3.dot v₁ u₂) ∧
      zornFisherMetric (zornReflE1 : ZornMatrix K) zornReflE2 = 0 ∧
      zornSymplecticForm (zornReflE1 : ZornMatrix K) zornReflE2 = 0 ∧
      zornMatrixDet (zornHodgeCross (zornReflE1 : ZornMatrix K) zornReflE2) = 1) ∧
    -- (2) Hodge cross-product determinant
    (zornMatrixDet (zornHodgeCross z₁ z₂) =
      Vec3.dot (Vec3.cross u₁ u₂) (Vec3.cross v₁ v₂)) ∧
    -- (3) Exact Three-Term Metriplectic Pythagorean Law
    (4 * zornMatrixDet (z₁ * z₂) =
        zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
          zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ +
          4 * zornMatrixDet (zornHodgeCross z₁ z₂) ∧
      zornFisherMetric z₁ z₂ * zornFisherMetric z₁ z₂ -
          zornSymplecticForm z₁ z₂ * zornSymplecticForm z₁ z₂ +
          4 * zornMatrixDet (zornHodgeCross z₁ z₂) =
        4 * (zornMatrixDet z₁ * zornMatrixDet z₂)) := by
  intro z₁ z₂
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · dsimp [z₁, z₂, zornTangent, zornFisherMetric, zornSymplecticForm, Vec3.dot]; ring
  · simp [zornFisherMetric, zornReflE1, zornReflE2, Vec3.dot]
  · simp [zornSymplecticForm, zornReflE1, zornReflE2, Vec3.dot]
  · simp [zornMatrixDet, zornHodgeCross, zornReflE1, zornReflE2,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
  · simp [z₁, z₂, zornTangent, zornMatrixDet, zornHodgeCross,
      Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [z₁, z₂, zornTangent, zornMatrixDet, zornFisherMetric, zornSymplecticForm,
      zornHodgeCross, ZornMatrix.mul, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · simp [z₁, z₂, zornTangent, zornMatrixDet, zornFisherMetric, zornSymplecticForm,
      zornHodgeCross, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring

-- theorem-class: constructive endpoint
/-- **Stages `𝔐ℨ₅, 𝔐ℨ₆` Theorem
(`stage_MZ5_MZ6_third_order_baryon_and_associator_volume_duality`)**:
For three tangent elements `z_i = zornTangent u_i v_i` (`i = 1, 2, 3`) over `[CommRing K]`
and non-commutative vector `u_nc : Vec3 R` over `[Ring R]`:
1. **Stage `𝔐ℨ₅` Part A — Cubic Baryon Volume on the DeWitt Sum `1`**:
   * `(zornHodgeCross z₁ z₂) * z₃ + z₃ * (zornHodgeCross z₁ z₂) =
        zornMatrixScalar (zornFisherMetric (zornHodgeCross z₁ z₂) z₃)`,
   * `(zornHodgeCross z₁ z₂) * z₃ + z₃ * (zornHodgeCross z₁ z₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃ - zornVec3Det v₁ v₂ v₃)`.
2. **Stage `𝔐ℨ₅` Part B — Cubic Associator Volume on the DeWitt Difference `I_para`**:
   * `zornDiagPart (zornAssoc z₁ z₂ z₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) * zornIPara)`,
   * `zornMatrixTrace (zornAssoc z₁ z₂ z₃) = 0` (the diagonal associator of three tangent Zorn
     vectors is 100% polarized along `I_para = u₀ - u₀*`!).
3. **Stage `𝔐ℨ₆` — Non-Commutative Nambu Associator Specialization over `[Ring R]`**:
   `zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
     -(scalarZorn (Vec3.nambu3 u_nc) * zornIPara)`. -/
theorem stage_MZ5_MZ6_third_order_baryon_and_associator_volume_duality
    (u₁ v₁ u₂ v₂ u₃ v₃ : Vec3 K) (u_nc : Vec3 R) :
    let z₁ := zornTangent u₁ v₁
    let z₂ := zornTangent u₂ v₂
    let z₃ := zornTangent u₃ v₃
    -- (1) Cubic baryon volume on 1 (DeWitt Sum)
    ((zornHodgeCross z₁ z₂) * z₃ + z₃ * (zornHodgeCross z₁ z₂) =
        zornMatrixScalar (zornFisherMetric (zornHodgeCross z₁ z₂) z₃) ∧
      (zornHodgeCross z₁ z₂) * z₃ + z₃ * (zornHodgeCross z₁ z₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃ - zornVec3Det v₁ v₂ v₃)) ∧
    -- (2) Cubic associator volume on I_para (DeWitt Difference) & trace vanishing
    (zornDiagPart (zornAssoc z₁ z₂ z₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) * zornIPara) ∧
      zornMatrixTrace (zornAssoc z₁ z₂ z₃) = 0) ∧
    -- (3) Non-commutative Nambu associator specialization over [Ring R]
    (zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
      -(scalarZorn (Vec3.nambu3 u_nc) * zornIPara)) := by
  intro z₁ z₂ z₃
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · ext <;> simp [z₁, z₂, z₃, zornTangent, zornHodgeCross, zornMatrixScalar,
      zornFisherMetric, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [z₁, z₂, z₃, zornTangent, zornHodgeCross, zornMatrixScalar,
      zornVec3Det, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.smulLeft, Vec3.smulRight] <;> ring
  · ext <;> simp [z₁, z₂, z₃, zornTangent, zornDiagPart, zornAssoc,
      zornMatrixScalar, zornVec3Det, zornIPara, ZornMatrix.gamma5,
      ZornMatrix.mul, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight] <;> ring
  · simp [z₁, z₂, z₃, zornTangent, zornMatrixTrace, zornAssoc,
      ZornMatrix.mul, Vec3.dot, Vec3.cross, Vec3.smulLeft, Vec3.smulRight]
    ring
  · dsimp [zornAssoc, scalarZorn, zornIPara]
    zorn_ring

-- theorem-class: capstone consumer theorem
/-- **Master Metriplectic Zorn Three-Channel & Volume Duality Theorem
(`metriplectic_zorn_three_channel_pythagorean_volume_master_poset`)**:
Bundles the 6-stage poset `𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`. -/
theorem metriplectic_zorn_three_channel_pythagorean_volume_master_poset
    (z₁ z₂ : ZornMatrix R) (u_nc : Vec3 R)
    (u₁ v₁ u₂ v₂ u₃ v₃ : Vec3 K) :
    let t₁ := zornTangent u₁ v₁
    let t₂ := zornTangent u₂ v₂
    let t₃ := zornTangent u₃ v₃
    -- (1) Poset acyclicity of 𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆
    (∀ st : MetriplecticZornStage,
      ¬ Relation.TransGen MetriplecticZornStage.causalEdge st st) ∧
    -- (2) Stages 𝔐ℨ₁–𝔐ℨ₃: Three-channel decomposition, Para-Kähler locking & Jordan-Malcev split
    (zornFisherMetric (zornIPara * z₁) z₂ = zornSymplecticForm z₁ z₂ ∧
      z₁ * z₂ + z₁ * z₂ =
        scalarZorn (zornFisherMetric z₁ z₂) +
          scalarZorn (zornSymplecticForm z₁ z₂) * zornIPara +
          (zornHodgeCross z₁ z₂ + zornHodgeCross z₁ z₂) ∧
      t₁ * t₂ + t₂ * t₁ = zornMatrixScalar (zornFisherMetric t₁ t₂) ∧
      t₁ * t₂ - t₂ * t₁ =
        zornMatrixScalar (zornSymplecticForm t₁ t₂) * zornIPara +
          (zornHodgeCross t₁ t₂ + zornHodgeCross t₁ t₂)) ∧
    -- (3) Stage 𝔐ℨ₄: Three-Term Metriplectic Pythagorean Determinant Law
    (4 * zornMatrixDet (t₁ * t₂) =
        zornFisherMetric t₁ t₂ * zornFisherMetric t₁ t₂ -
          zornSymplecticForm t₁ t₂ * zornSymplecticForm t₁ t₂ +
          4 * zornMatrixDet (zornHodgeCross t₁ t₂) ∧
      zornFisherMetric t₁ t₂ * zornFisherMetric t₁ t₂ -
          zornSymplecticForm t₁ t₂ * zornSymplecticForm t₁ t₂ +
          4 * zornMatrixDet (zornHodgeCross t₁ t₂) =
        4 * (zornMatrixDet t₁ * zornMatrixDet t₂)) ∧
    -- (4) Stages 𝔐ℨ₅–𝔐ℨ₆: Third-Order Baryon/Associator Volume Duality & Nambu Specialization
    ((zornHodgeCross t₁ t₂) * t₃ + t₃ * (zornHodgeCross t₁ t₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃ - zornVec3Det v₁ v₂ v₃) ∧
      zornDiagPart (zornAssoc t₁ t₂ t₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) * zornIPara) ∧
      zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
        -(scalarZorn (Vec3.nambu3 u_nc) * zornIPara)) := by
  intro t₁ t₂ t₃
  have hMZ13 :=
    stage_MZ1_MZ2_MZ3_metriplectic_three_channel_decomposition_and_jordan_malcev_split
      z₁ z₂ u₁ v₁ u₂ v₂
  have hMZ4 := stage_MZ4_three_term_metriplectic_pythagorean_norm_law u₁ v₁ u₂ v₂
  have hMZ56 :=
    stage_MZ5_MZ6_third_order_baryon_and_associator_volume_duality
      u₁ v₁ u₂ v₂ u₃ v₃ u_nc
  exact ⟨MetriplecticZornStage.causalEdge_acyclic,
    ⟨hMZ13.1.2.2.2, hMZ13.2.1, hMZ13.2.2.2.2.2.1, hMZ13.2.2.2.2.2.2⟩,
    ⟨hMZ4.2.2.1, hMZ4.2.2.2⟩,
    ⟨hMZ56.1.2, hMZ56.2.1.1, hMZ56.2.2⟩⟩

end MetriplecticZornThreeChannelClosure

/-! ===========================================================================
    Section 7c: The 6-Stage Operator Madelung–Bohm Split, Firth–Zorn Trilinear
    Contextual Semantics, & Gauge-Dark / Gravity-Active Chiral Condensate Poset
    (`𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ 𝔐𝔅₃ ≺ 𝔐𝔅₄ ≺ {𝔐𝔅₅, 𝔐𝔅₆}`)
    =========================================================================== -/

/-- The 6 stages of the **Operator Madelung–Bohm Split, Firth–Zorn Trilinear Contextual
Semantics, & Gauge-Dark / Gravity-Active Chiral Condensate Poset**
(`𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ 𝔐𝔅₃ ≺ 𝔐𝔅₄ ≺ {𝔐𝔅₅, 𝔐𝔅₆}`). -/
inductive MadelungBohmFirthDarkGravityStage : Type
  | mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude
  | mb2_operator_bohm_quantum_force_and_chiral_beat_clocking
  | mb3_firth_trilinear_contextual_semantics_in_zorn_matrix
  | mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff
  | mb5_internal_gauge_darkness_in_even_core
  | mb6_gravitational_frame_dragging_and_curvature_on_odd_frame
  deriving DecidableEq, Repr, Inhabited

namespace MadelungBohmFirthDarkGravityStage

/-- Direct causal cover relation for `𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ 𝔐𝔅₃ ≺ 𝔐𝔅₄ ≺ {𝔐𝔅₅, 𝔐𝔅₆}`. -/
def causalEdge : MadelungBohmFirthDarkGravityStage → MadelungBohmFirthDarkGravityStage → Prop
  | .mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude,
      .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking => True
  | .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking,
      .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix => True
  | .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix,
      .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff => True
  | .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff,
      .mb5_internal_gauge_darkness_in_even_core => True
  | .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff,
      .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> simp [causalEdge] <;> infer_instance

/-- Strictly increasing topological rank of `MadelungBohmFirthDarkGravityStage`. -/
def toIndex : MadelungBohmFirthDarkGravityStage → ℕ
  | .mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude => 0
  | .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking => 1
  | .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix => 2
  | .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff => 3
  | .mb5_internal_gauge_darkness_in_even_core => 4
  | .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame => 5

theorem toIndex_injective : Function.Injective toIndex := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder MadelungBohmFirthDarkGravityStage :=
  LinearOrder.lift' toIndex toIndex_injective

instance : Fintype MadelungBohmFirthDarkGravityStage where
  elems := {
    .mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude,
    .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking,
    .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix,
    .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff,
    .mb5_internal_gauge_darkness_in_even_core,
    .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card MadelungBohmFirthDarkGravityStage = 6 := rfl

theorem causalEdge_lt {a b : MadelungBohmFirthDarkGravityStage} (h : causalEdge a b) :
    a.toIndex < b.toIndex := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : MadelungBohmFirthDarkGravityStage} (h : Relation.TransGen causalEdge a b) :
    a.toIndex < b.toIndex := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_lt h2)

/-- **Poset Acyclicity Theorem**: The 6-stage poset `𝔐𝔅₁ ≺ ⋯ ≺ 𝔐𝔅₆` has no directed cycles. -/
theorem causalEdge_acyclic (s : MadelungBohmFirthDarkGravityStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl s.toIndex (transGen_lt h)

theorem not_causalEdge_from_mb5 (b : MadelungBohmFirthDarkGravityStage) :
    ¬ causalEdge .mb5_internal_gauge_darkness_in_even_core b := by
  cases b <;> decide

theorem not_transGen_from_mb5 {a b : MadelungBohmFirthDarkGravityStage}
    (h : Relation.TransGen causalEdge a b)
    (ha : a = .mb5_internal_gauge_darkness_in_even_core) : False := by
  induction h with
  | single h1 =>
    rw [ha] at h1
    exact not_causalEdge_from_mb5 _ h1
  | tail _ _ ih => exact ih

/-- **Parallel Branch Theorem**: `𝔐𝔅₅` (Gauge Darkness in `𝔨`) and `𝔐𝔅₆` (Gravitational
Frame Dragging on `𝔭`) form a genuine incomparable bifurcation above `𝔐𝔅₄`. -/
theorem incomparable_MB5_MB6 :
    ¬ Relation.TransGen causalEdge
        .mb5_internal_gauge_darkness_in_even_core
        .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame ∧
      ¬ Relation.TransGen causalEdge
        .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame
        .mb5_internal_gauge_darkness_in_even_core := by
  refine ⟨?_, ?_⟩
  · intro h
    exact not_transGen_from_mb5 h rfl
  · intro h
    exact Nat.not_lt.mpr (by decide : (4 : ℕ) ≤ 5) (transGen_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : MadelungBohmFirthDarkGravityStage → RepDepth
  | .mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude => .operator
  | .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking => .operator
  | .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix => .transport
  | .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff => .transport
  | .mb5_internal_gauge_darkness_in_even_core => .thermo
  | .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame => .thermo

theorem toRepDepth_mono {a b : MadelungBohmFirthDarkGravityStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : MadelungBohmFirthDarkGravityStage → OntologyMetaLevel
  | .mb1_operator_madelung_bohm_split_phase_vs_osmotic_amplitude => .M1_ProjectorClabject
  | .mb2_operator_bohm_quantum_force_and_chiral_beat_clocking => .M1_ProjectorClabject
  | .mb3_firth_trilinear_contextual_semantics_in_zorn_matrix => .M2_GrassmannianPowertypeOrbit
  | .mb4_parafermion_and_nambu_associator_condensation_onto_dewitt_diff => .M2_GrassmannianPowertypeOrbit
  | .mb5_internal_gauge_darkness_in_even_core => .M3_ErlangenCasimirMetaLaw
  | .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : MadelungBohmFirthDarkGravityStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end MadelungBohmFirthDarkGravityStage

section MadelungBohmFirthDarkGravityClosure

variable {B : Type*} [Ring B]
variable {R : Type*} [Ring R]
variable {K : Type*} [CommRing K]

/-- Operator Bohm restorative quantum force on an observable `X : B` generated by the
osmotic amplitude bridge `Φ`:
`operatorBohmForce Φ X := -[Φ, [Φ, X]]`. -/
def operatorBohmForce (Phi X : B) : B :=
  -comm Phi (comm Phi X)

/-- Dual restorative force on an observable `X : B` generated by the classical phase current `J`:
`operatorPhaseForce J X := -[J, [J, X]]`. -/
def operatorPhaseForce (J X : B) : B :=
  -comm J (comm J X)

/-- Chiral DeWitt Difference / grading involution `S_P = 2P - 1 = invS P`. -/
abbrev gradingOp (P : B) : B :=
  invS P

/-- General two-seed block-diagonal internal gauge boson
`Ω_EM(P, W₁, W₂) = P W₁ P + (1 - P) W₂ (1 - P) ∈ 𝔨`. -/
def evenCore (P W₁ W₂ : B) : B :=
  P * W₁ * P + (1 - P) * W₂ * (1 - P)

/-- Chiral / associator condensate polarized along the DeWitt Difference `I_para = u₀ - u₀*`:
`zornChiralCondensate ρ := scalarZorn ρ * zornIPara = diag(ρ, -ρ)`. -/
def zornChiralCondensate (ρ : R) : ZornMatrix R :=
  scalarZorn ρ * zornIPara

/-- Internal block-diagonal gauge boson `Ω_EM(a, d) := a e_L + d e_R = diag(a, d) ∈ 𝔨`
in `ZornMatrix R`. -/
def zornInternalGaugeField (a d : R) : ZornMatrix R :=
  scalarZorn a * ZornMatrix.eL + scalarZorn d * ZornMatrix.eR

/-- Spacetime osmotic amplitude bridge / solder form `Φ(u, v) := N_+(u) + N_-(v) ∈ 𝔭`
in `ZornMatrix R`. -/
def zornOsmoticFrame (u v : Vec3 R) : ZornMatrix R :=
  ZornMatrix.psiPlus u + ZornMatrix.psiMinus v

/-- Spacetime classical phase current `J(u, v) := N_+(u) - N_-(v) ∈ 𝔭` in `ZornMatrix R`. -/
def zornPhaseCurrent (u v : Vec3 R) : ZornMatrix R :=
  ZornMatrix.psiPlus u - ZornMatrix.psiMinus v

-- theorem-class: constructive endpoint
/-- **Rung 0 & Stages `𝔐𝔅₁, 𝔐𝔅₂` Theorem
(`stage_MB1_MB2_operator_madelung_bohm_split_bohm_force_and_chiral_beat`)**:
1. **Rung 0 Socratic Aporia of Commutative Hydrodynamics**:
   * For any commuting elements `r s : B` (`r * s = s * r`), `comm r s = 0`,
   * In any associative ring `B`, `(A * C) * W - A * (C * W) = 0`.
2. **Stage `𝔐𝔅₁` (Operator Madelung–Bohm Split: Phase `J` vs. Osmotic Bohm Amplitude `Φ`)**:
   For any idempotent `P * P = P` and seeds `A C : B`:
   * `genJ P A C * genJ P A C = -genV P A C` (timelike classical kinetic square `J² = -V`),
   * `genPhi P A C * genPhi P A C = genV P A C` (spacelike operator Bohm potential `Φ² = +V`),
   * `genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0`,
   * `comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)` (`[Φ, J] = -2 Σ`),
   * `anticomm (genPhi P A C) (genJ P A C) = 0` (`{Φ, J} = 0`).
3. **Stage `𝔐𝔅₂` (Operator Bohm Restorative Force & Yin–Yang Chiral Beat Clocking)**:
   * `comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)` (`[Σ, Φ] = 2 V J`),
   * `comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)` (`[Σ, J] = 2 V Φ`),
   * `operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((2 : ℤ) • comm (genSig P A C) (genPhi P A C))` (`-[Φ, [Φ, J]] = -2 [Σ, Φ]`),
   * `operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((4 : ℤ) • (genV P A C * genJ P A C))` (`-[Φ, [Φ, J]] = -4 V J`),
   * `operatorPhaseForce (genJ P A C) (genPhi P A C) =
        (4 : ℤ) • (genV P A C * genPhi P A C)` (`-[J, [J, Φ]] = 4 V Φ`),
   * `(W + genPhi P A C) * (W + genPhi P A C) =
        (W * W + genV P A C) + anticomm W (genPhi P A C)` (`(Ω + Φ)² = (Ω² + V) + {Ω, Φ}`). -/
theorem stage_MB1_MB2_operator_madelung_bohm_split_bohm_force_and_chiral_beat
    {P : B} (hP : P * P = P) (A C W : B)
    {r s : B} (hrs : r * s = s * r) :
    -- (1) Rung 0 Commutative / Associative Aporia
    (comm r s = 0 ∧ (A * C) * W - A * (C * W) = 0) ∧
    -- (2) Stage 𝔐𝔅₁: Operator Madelung-Bohm Split (J² = -V, Φ² = +V, [Φ, J] = -2Σ, {Φ, J} = 0)
    (genJ P A C * genJ P A C = -genV P A C ∧
      genPhi P A C * genPhi P A C = genV P A C ∧
      genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
      comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
      anticomm (genPhi P A C) (genJ P A C) = 0) ∧
    -- (3) Stage 𝔐𝔅₂: Operator Bohm Quantum Force & Yin-Yang Chiral Beat Clocking
    (comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
      comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
      operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
      operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
      operatorPhaseForce (genJ P A C) (genPhi P A C) =
        (4 : ℤ) • (genV P A C * genPhi P A C) ∧
      (W + genPhi P A C) * (W + genPhi P A C) =
        (W * W + genV P A C) + anticomm W (genPhi P A C)) := by
  refine ⟨⟨by change r * s - s * r = 0; rw [hrs, sub_self],
           by rw [mul_assoc, sub_self]⟩,
    ⟨by peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP⟩,
    ⟨by peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP,
     by dsimp [operatorBohmForce]; peirce_abel_znd3 hP,
     by dsimp [operatorBohmForce]; peirce_abel_znd3 hP,
     by dsimp [operatorPhaseForce]; peirce_abel_znd3 hP,
     by peirce_abel_znd3 hP⟩⟩

/-- Diagonal trace `a + d` on `ZornMatrix K`. -/
abbrev zornTrace (X : ZornMatrix K) : K :=
  zornMatrixTrace X

-- theorem-class: constructive endpoint
/-- **Stages `𝔐𝔅₃, 𝔐𝔅₄` Theorem
(`stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation`)**:
1. **Stage `𝔐𝔅₃` (Firth's Distributional Contextual Law in `ZornMatrix K`)**:
   * **1-Body Isolation (Void)**:
     `ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₁ = 0`,
     `zornTrace (ZornMatrix.psiPlus u₁) = 0`,
     `zornMatrixDet (ZornMatrix.psiPlus u₁) = 0`,
     `zornDiagPart (ZornMatrix.psiPlus u₁) = 0`.
   * **2-Body Syntactic Company (Off-Diagonal Diquark Jump, Still Zero Diagonal/Trace)**:
     `ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂ = ZornMatrix.psiMinus (Vec3.cross u₁ u₂)`,
     `zornTrace (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) = 0`,
     `zornDiagPart (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) = 0`.
   * **3-Body Semantic Company (Non-Zero Volume Precipitation onto `1` and `I_para`)**:
     `(ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) * ZornMatrix.psiPlus u₃ +
        ZornMatrix.psiPlus u₃ * (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃)`,
     `zornAssoc (ZornMatrix.psiPlus u₁) (ZornMatrix.psiPlus u₂) (ZornMatrix.psiPlus u₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃) * zornIPara)`.
   * **Standard Basis Triad `(eX, eY, eZ)` Witness**:
     `(ZornMatrix.psiPlus (Vec3.eX : Vec3 ℤ) * ZornMatrix.psiPlus Vec3.eY) *
        ZornMatrix.psiPlus Vec3.eZ +
      ZornMatrix.psiPlus Vec3.eZ *
        (ZornMatrix.psiPlus Vec3.eX * ZornMatrix.psiPlus Vec3.eY) =
      (1 : ZornMatrix ℤ)`,
     `zornAssoc (ZornMatrix.psiPlus (Vec3.eX : Vec3 ℤ))
        (ZornMatrix.psiPlus Vec3.eY) (ZornMatrix.psiPlus Vec3.eZ) =
      -(zornIPara : ZornMatrix ℤ)`.
2. **Stage `𝔐𝔅₄` (Chiral Associator & Nambu Condensation onto `I_para`)**:
   * `zornDiagPart (zornAssoc (zornTangent u₁ v₁) (zornTangent u₂ v₂) (zornTangent u₃ v₃)) =
        -zornChiralCondensate (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃)`,
   * `zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
        -zornChiralCondensate (Vec3.nambu3 u_nc)`. -/
theorem stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation
    (u₁ u₂ u₃ v₁ v₂ v₃ : Vec3 K) (u_nc : Vec3 R) :
    -- (1) 1-Body Isolation (Void)
    (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₁ = 0 ∧
      zornTrace (ZornMatrix.psiPlus u₁) = 0 ∧
      zornMatrixDet (ZornMatrix.psiPlus u₁) = 0 ∧
      zornDiagPart (ZornMatrix.psiPlus u₁) = 0) ∧
    -- (2) 2-Body Syntactic Company (Diquark Jump, Zero Diagonal/Trace)
    (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂ = ZornMatrix.psiMinus (Vec3.cross u₁ u₂) ∧
      zornTrace (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) = 0 ∧
      zornDiagPart (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) = 0) ∧
    -- (3) 3-Body Semantic Company (Volume Precipitation onto 1 and I_para)
    ((ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) * ZornMatrix.psiPlus u₃ +
        ZornMatrix.psiPlus u₃ * (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃) ∧
      zornAssoc (ZornMatrix.psiPlus u₁) (ZornMatrix.psiPlus u₂) (ZornMatrix.psiPlus u₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃) * zornIPara) ∧
      (ZornMatrix.psiPlus (Vec3.eX : Vec3 ℤ) * ZornMatrix.psiPlus Vec3.eY) *
          ZornMatrix.psiPlus Vec3.eZ +
        ZornMatrix.psiPlus Vec3.eZ *
          (ZornMatrix.psiPlus Vec3.eX * ZornMatrix.psiPlus Vec3.eY) =
        (1 : ZornMatrix ℤ) ∧
      zornAssoc (ZornMatrix.psiPlus (Vec3.eX : Vec3 ℤ))
          (ZornMatrix.psiPlus Vec3.eY) (ZornMatrix.psiPlus Vec3.eZ) =
        -(zornIPara : ZornMatrix ℤ)) ∧
    -- (4) Stage 𝔐𝔅₄: General Tangent & Non-Commutative Nambu Associator Condensation
    (zornDiagPart (zornAssoc (zornTangent u₁ v₁) (zornTangent u₂ v₂) (zornTangent u₃ v₃)) =
        -zornChiralCondensate (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) ∧
      zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
        -zornChiralCondensate (Vec3.nambu3 u_nc)) := by
  have hMZ56 :=
    stage_MZ5_MZ6_third_order_baryon_and_associator_volume_duality
      u₁ v₁ u₂ v₂ u₃ v₃ u_nc
  have hPsiMul :
      ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂ =
        ZornMatrix.psiMinus (Vec3.cross u₁ u₂) := by
    ext <;> simp [ZornMatrix.psiPlus, ZornMatrix.psiMinus, Vec3.dot, Vec3.cross]
  refine ⟨⟨by ext <;> simp [ZornMatrix.psiPlus, Vec3.dot, Vec3.cross] <;> ring,
           by simp [zornTrace, zornMatrixTrace, ZornMatrix.psiPlus],
           by simp [zornMatrixDet, ZornMatrix.psiPlus, Vec3.dot],
           by ext <;> rfl⟩,
    ⟨hPsiMul,
     by rw [hPsiMul]; simp [zornTrace, zornMatrixTrace, ZornMatrix.psiMinus],
     by rw [hPsiMul]; ext <;> rfl⟩,
    ⟨by
       (ext <;>
         simp [ZornMatrix.psiPlus, zornMatrixScalar, zornVec3Det,
           Vec3.dot, Vec3.cross])
       ring,
     by
       (ext <;>
         simp [zornAssoc, ZornMatrix.psiPlus, zornMatrixScalar, zornIPara,
           ZornMatrix.gamma5, zornVec3Det, Vec3.dot, Vec3.cross])
       ring,
     by decide,
     by decide⟩,
    ⟨by
       dsimp [zornChiralCondensate, zornMatrixScalar]
       exact hMZ56.2.1.1,
     by
       dsimp [zornChiralCondensate]
       exact hMZ56.2.2⟩⟩

set_option maxHeartbeats 800000 in
-- theorem-class: constructive endpoint
/-- **Stages `𝔐𝔅₅, 𝔐𝔅₆` Theorem
(`stage_MB5_MB6_dark_gravity_dichotomy_gauge_dark_yet_frame_dragging`)**:
1. **Universal Operator Dark-Gravity Dichotomy in Any Associative Ring `B` with `P * P = P`**:
   * **Stage `𝔐𝔅₅` (Internal Gauge Darkness in `𝔨`)**:
     For any internal block-diagonal gauge boson `Ω_EM = evenCore P W₁ W₂`:
     `comm (gradingOp P) (evenCore P W₁ W₂) = 0` (`[S_P, Ω_EM] = 0`).
   * **Stage `𝔐𝔅₆` (Gravitational Frame Dragging & Curvature on `𝔭`)**:
     `anticomm (gradingOp P) (genPhi P A C) = 0` (`{S_P, Φ} = 0`),
     `anticomm (gradingOp P) (genJ P A C) = 0` (`{S_P, J} = 0`),
     `comm (gradingOp P) (genPhi P A C) = (2 : ℤ) • genJ P A C` (`[S_P, Φ] = 2 J`),
     `comm (gradingOp P) (genJ P A C) = (2 : ℤ) • genPhi P A C` (`[S_P, J] = 2 Φ`),
     `comm (gradingOp P) (comm (gradingOp P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C`
       (`[S_P, [S_P, Φ]] = 4 Φ`),
     `comm (gradingOp P) (comm (gradingOp P) (genJ P A C)) = (4 : ℤ) • genJ P A C`
       (`[S_P, [S_P, J]] = 4 J`).
2. **Concrete Zorn Split-Octonion Condensate `Σ_DM(ρ) = zornChiralCondensate ρ` over `[CommRing K]`**:
   * **Gauge Darkness in `𝔨`**:
     `zornChiralCondensate ρ * zornInternalGaugeField a d -
        zornInternalGaugeField a d * zornChiralCondensate ρ = 0`,
   * **Linear Gravitational Frame Dragging on `𝔭`**:
     `zornChiralCondensate ρ * zornOsmoticFrame u₁ v₁ -
        zornOsmoticFrame u₁ v₁ * zornChiralCondensate ρ =
        zornMatrixScalar (2 * ρ) * zornPhaseCurrent u₁ v₁`,
     `zornChiralCondensate ρ * zornPhaseCurrent u₁ v₁ -
        zornPhaseCurrent u₁ v₁ * zornChiralCondensate ρ =
        zornMatrixScalar (2 * ρ) * zornOsmoticFrame u₁ v₁`,
   * **Quadratic Gravitational Curvature on `𝔭`**:
     `let c1 := zornChiralCondensate ρ * zornOsmoticFrame u₁ v₁ -
                  zornOsmoticFrame u₁ v₁ * zornChiralCondensate ρ
      zornChiralCondensate ρ * c1 - c1 * zornChiralCondensate ρ =
        zornMatrixScalar (4 * ρ * ρ) * zornOsmoticFrame u₁ v₁`. -/
theorem stage_MB5_MB6_dark_gravity_dichotomy_gauge_dark_yet_frame_dragging
    {P : B} (hP : P * P = P) (A C W₁ W₂ : B)
    (ρ a d : K) (u₁ v₁ : Vec3 K) :
    -- (1) Universal Operator Dark-Gravity Dichotomy in B
    (comm (gradingOp P) (evenCore P W₁ W₂) = 0 ∧
      anticomm (gradingOp P) (genPhi P A C) = 0 ∧
      anticomm (gradingOp P) (genJ P A C) = 0 ∧
      comm (gradingOp P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
      comm (gradingOp P) (genJ P A C) = (2 : ℤ) • genPhi P A C ∧
      comm (gradingOp P) (comm (gradingOp P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C ∧
      comm (gradingOp P) (comm (gradingOp P) (genJ P A C)) = (4 : ℤ) • genJ P A C) ∧
    -- (2) Concrete Zorn Split-Octonion Condensate Dark-Gravity Dichotomy
    (zornChiralCondensate ρ * zornInternalGaugeField a d -
        zornInternalGaugeField a d * zornChiralCondensate ρ = 0 ∧
      zornChiralCondensate ρ * zornOsmoticFrame u₁ v₁ -
          zornOsmoticFrame u₁ v₁ * zornChiralCondensate ρ =
        zornMatrixScalar (2 * ρ) * zornPhaseCurrent u₁ v₁ ∧
      zornChiralCondensate ρ * zornPhaseCurrent u₁ v₁ -
          zornPhaseCurrent u₁ v₁ * zornChiralCondensate ρ =
        zornMatrixScalar (2 * ρ) * zornOsmoticFrame u₁ v₁ ∧
      (let c1 := zornChiralCondensate ρ * zornOsmoticFrame u₁ v₁ -
                   zornOsmoticFrame u₁ v₁ * zornChiralCondensate ρ
       zornChiralCondensate ρ * c1 - c1 * zornChiralCondensate ρ =
         zornMatrixScalar (4 * ρ * ρ) * zornOsmoticFrame u₁ v₁)) := by
  refine ⟨⟨by dsimp [gradingOp, evenCore]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP,
           by dsimp [gradingOp]; peirce_abel_znd3 hP⟩,
    ⟨by
       ext <;>
         simp [zornChiralCondensate, zornInternalGaugeField, scalarZorn, zornIPara,
           ZornMatrix.gamma5, ZornMatrix.eL, ZornMatrix.eR,
           Vec3.dot, Vec3.cross] <;>
         ring,
     by
       ext <;>
         simp [zornChiralCondensate, zornOsmoticFrame, zornPhaseCurrent, zornMatrixScalar,
           scalarZorn, zornIPara, ZornMatrix.gamma5, ZornMatrix.psiPlus, ZornMatrix.psiMinus,
           Vec3.dot, Vec3.cross] <;>
         ring,
     by
       ext <;>
         simp [zornChiralCondensate, zornOsmoticFrame, zornPhaseCurrent, zornMatrixScalar,
           scalarZorn, zornIPara, ZornMatrix.gamma5, ZornMatrix.psiPlus, ZornMatrix.psiMinus,
           Vec3.dot, Vec3.cross] <;>
         ring,
     by
       dsimp only
       ext <;>
         simp [zornChiralCondensate, zornOsmoticFrame, zornMatrixScalar,
           scalarZorn, zornIPara, ZornMatrix.gamma5, ZornMatrix.psiPlus, ZornMatrix.psiMinus,
           Vec3.dot, Vec3.cross] <;>
         ring⟩⟩

-- theorem-class: capstone consumer theorem
/-- **Master Operator Madelung–Bohm, Firth Trilinear Contextuality, & Dark-Gravity Theorem
(`madelung_bohm_firth_chiral_dark_gravity_master_poset`)**:
Unifies the 6-stage poset `𝔐𝔅₁ ≺ 𝔐𝔅₂ ≺ 𝔐𝔅₃ ≺ 𝔐𝔅₄ ≺ {𝔐𝔅₅, 𝔐𝔅₆}`. -/
theorem madelung_bohm_firth_chiral_dark_gravity_master_poset
    {P : B} (hP : P * P = P) (A C W₁ W₂ : B)
    (ρ a d : K) (u₁ u₂ u₃ v₁ v₂ v₃ : Vec3 K) (u_nc : Vec3 R) :
    -- (1) Poset acyclicity and parallel branch incomparability
    ((∀ st : MadelungBohmFirthDarkGravityStage,
        ¬ Relation.TransGen MadelungBohmFirthDarkGravityStage.causalEdge st st) ∧
      (¬ Relation.TransGen MadelungBohmFirthDarkGravityStage.causalEdge
          .mb5_internal_gauge_darkness_in_even_core
          .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame ∧
        ¬ Relation.TransGen MadelungBohmFirthDarkGravityStage.causalEdge
          .mb6_gravitational_frame_dragging_and_curvature_on_odd_frame
          .mb5_internal_gauge_darkness_in_even_core)) ∧
    -- (2) Stages 𝔐𝔅₁, 𝔐𝔅₂: Operator Madelung-Bohm split & Bohm restorative force
    (genJ P A C * genJ P A C = -genV P A C ∧
      genPhi P A C * genPhi P A C = genV P A C ∧
      operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
      operatorBohmForce (genPhi P A C) (genJ P A C) =
        -((4 : ℤ) • (genV P A C * genJ P A C))) ∧
    -- (3) Stages 𝔐𝔅₃, 𝔐𝔅₄: Firth 1/2/3-body contextuality & associator condensation
    (zornTrace (ZornMatrix.psiPlus u₁) = 0 ∧
      zornTrace (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) = 0 ∧
      (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) * ZornMatrix.psiPlus u₃ +
          ZornMatrix.psiPlus u₃ * (ZornMatrix.psiPlus u₁ * ZornMatrix.psiPlus u₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃) ∧
      zornDiagPart (zornAssoc (zornTangent u₁ v₁) (zornTangent u₂ v₂) (zornTangent u₃ v₃)) =
        -zornChiralCondensate (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) ∧
      zornAssoc (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) (ZornMatrix.psiPlus u_nc) =
        -zornChiralCondensate (Vec3.nambu3 u_nc)) ∧
    -- (4) Stages 𝔐𝔅₅, 𝔐𝔅₆: Gauge darkness in 𝔨 & gravitational frame dragging on 𝔭
    (comm (gradingOp P) (evenCore P W₁ W₂) = 0 ∧
      comm (gradingOp P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
      comm (gradingOp P) (comm (gradingOp P) (genPhi P A C)) = (4 : ℤ) • genPhi P A C ∧
      zornChiralCondensate ρ * zornInternalGaugeField a d -
          zornInternalGaugeField a d * zornChiralCondensate ρ = 0 ∧
      zornChiralCondensate ρ * zornOsmoticFrame u₁ v₁ -
          zornOsmoticFrame u₁ v₁ * zornChiralCondensate ρ =
        zornMatrixScalar (2 * ρ) * zornPhaseCurrent u₁ v₁) := by
  have hMB12 :=
    stage_MB1_MB2_operator_madelung_bohm_split_bohm_force_and_chiral_beat
      hP A C W₁ (r := 0) (s := 0) rfl
  have hMB34 :=
    stage_MB3_MB4_firth_trilinear_contextual_semantics_and_associator_condensation
      u₁ u₂ u₃ v₁ v₂ v₃ u_nc
  have hMB56 :=
    stage_MB5_MB6_dark_gravity_dichotomy_gauge_dark_yet_frame_dragging
      hP A C W₁ W₂ ρ a d u₁ v₁
  exact ⟨⟨MadelungBohmFirthDarkGravityStage.causalEdge_acyclic,
          MadelungBohmFirthDarkGravityStage.incomparable_MB5_MB6⟩,
    ⟨hMB12.2.1.1, hMB12.2.1.2.1, hMB12.2.2.2.2.1, hMB12.2.2.2.2.2.1⟩,
    ⟨hMB34.1.2.1, hMB34.2.1.2.1, hMB34.2.2.1.1, hMB34.2.2.2.1, hMB34.2.2.2.2⟩,
    ⟨hMB56.1.1, hMB56.1.2.2.2.1, hMB56.1.2.2.2.2.2.1, hMB56.2.1, hMB56.2.2.1⟩⟩

end MadelungBohmFirthDarkGravityClosure

/-! ===========================================================================
    Section 8: Master Capstone Theorem Unifying `𝔒₁ ≺ … ≺ 𝔒₇` with
    First-Quantized Amari Operator Geometry (`𝔇₁ ≺ … ≺ 𝔇₇`, `𝔔₁ ≺ … ≺ 𝔔₆`)
    =========================================================================== -/

-- theorem-class: capstone consumer theorem
/-- **Master Capstone Theorem
(`split_octonion_isotropic_circular_amari_baryon_nambu_master_poset`)**:
Unifies the 7-stage Split-Octonion Isotropic Circular Amari–Baryon–Nambu Poset
(`𝔒₁ ≺ … ≺ 𝔒₇`) with First-Quantized Amari Operator Geometry (`𝔇₁ ≺ … ≺ 𝔇₇`
and `𝔔₁ ≺ … ≺ 𝔔₆`):
1. Acyclicity of `SplitOctonionIsotropicAmariStage`, `AmariDuallyFlatOperatorStage`,
   and `FirstQuantizedAmariStage`,
2. Bi-Lagrangian split metric non-degeneracy (`det(G_split) = -1 ≠ 0`) and Rung 1
   circular polarization nilpotency (`U₊² = U₋² = 0`, `{U₊, U₋} = 4 • 1`),
3. Maximal isotropy of `𝔫₊, 𝔫₋` (`{U(x), U(y)} = 0`, `{V(x), V(y)} = 0`) and exact
   ray exponential flatness (`ℰ₊(t₁ x) ℰ₊(t₂ x) = ℰ₊((t₁ + t₂) x)`),
4. Chiral DeWitt Sum/Difference separation (`{U(x), V(y)} = (x · y) I` vs.
   `[U(x), V(y)] = (x · y) S_P`), Trace-First Blindness (`Tr([U(x), V(y)]) = 0`),
   and Chiral Supertrace Recovery (`Tr(S_P [U(x), V(y)]) = Tr({U(x), V(y)})`),
5. Split-Octonion Diquark Hodge Dual (`N_+(x) N_+(y) = N_-(x × y)`), Amari–Chentsov
   Cubic Baryon Singlet (`{U(x) U(y), U(z)} = det(x, y, z) I`), and Non-Commutative
   Nambu Associator (`[N_+(u), N_+(u), N_+(u)]_assoc = -(scalarZorn ⟦u⟧ * γ₅)`). -/
theorem split_octonion_isotropic_circular_amari_baryon_nambu_master_poset
    {R : Type*} [Ring R] {K : Type*} [CommRing K]
    (u v : Vec3 R) (xk yk zk : ColorVec3 K) (t₁ t₂ : K) :
    -- (1) Poset acyclicity across 𝔒, 𝔇, and 𝔔
    ((∀ st : SplitOctonionIsotropicAmariStage,
        ¬ Relation.TransGen SplitOctonionIsotropicAmariStage.causalEdge st st) ∧
      (∀ dst : AmariDuallyFlatOperatorStage,
        ¬ Relation.TransGen AmariDuallyFlatOperatorStage.causalEdge dst dst) ∧
      (∀ qst : FirstQuantizedAmariStage,
        ¬ Relation.TransGen FirstQuantizedAmariStage.causalEdge qst qst)) ∧
    -- (2) Rung 0 Bi-Lagrangian split metric non-degeneracy
    (biLagrangianSplitMetric6 * biLagrangianSplitMetric6 =
        (1 : Matrix (Fin 6) (Fin 6) ℤ) ∧
      Matrix.det biLagrangianSplitMetric6 = -1) ∧
    -- (3) Stages 𝔒₁, 𝔒₂: Maximal isotropy & ray exponential group law
    (ZornAlgebra.anticommutator (ZornAlgebra.quarkU xk) (ZornAlgebra.quarkU yk) =
        ZornAlgebra.zero ∧
      ZornAlgebra.mul (zornExpPlus (ColorVec3.smul t₁ xk)) (zornExpPlus (ColorVec3.smul t₂ xk)) =
        zornExpPlus (ColorVec3.smul (t₁ + t₂) xk)) ∧
    -- (4) Stages 𝔒₃, 𝔒₄, 𝔒₅: DeWitt Sum Fisher Metric, DeWitt Diff Berry Curvature & Supertrace
    (ZornAlgebra.anticommutator (ZornAlgebra.quarkU xk) (ZornAlgebra.antiquarkV yk) =
        ZornAlgebra.smul (ColorVec3.dot xk yk) ZornAlgebra.one ∧
      ZornAlgebra.commutator (ZornAlgebra.quarkU xk) (ZornAlgebra.antiquarkV yk) =
        ZornAlgebra.smul (ColorVec3.dot xk yk) zornDeWittDiff ∧
      ZornAlgebra.trace (ZornAlgebra.commutator (ZornAlgebra.quarkU xk) (ZornAlgebra.antiquarkV yk)) = 0 ∧
      ZornAlgebra.trace
          (ZornAlgebra.mul zornDeWittDiff
            (ZornAlgebra.commutator (ZornAlgebra.quarkU xk) (ZornAlgebra.antiquarkV yk))) =
        ZornAlgebra.trace
          (ZornAlgebra.anticommutator (ZornAlgebra.quarkU xk) (ZornAlgebra.antiquarkV yk))) ∧
    -- (5) Stages 𝔒₆, 𝔒₇: Diquark dual, Amari–Chentsov cubic baryon tensor & Nambu associator
    (ZornMatrix.psiPlus u * ZornMatrix.psiPlus v = ZornMatrix.psiMinus (Vec3.cross u v) ∧
      amariChentsovBaryon xk yk zk =
        ZornAlgebra.smul (ColorVec3.baryonDet xk yk zk) ZornAlgebra.one ∧
      ZornMatrix.cubicAssociator (ZornMatrix.psiPlus u) =
        -(scalarZorn (Vec3.nambu3 u) * ZornMatrix.gamma5)) := by
  have hR0 := rung0_biLagrangian_isotropic_split_metric_nondegenerate
  have hO12 := stage_O1_O2_dewitt_vacuum_bimodule_isotropy_and_ray_exponentials xk yk t₁ t₂ 0 0
  have hO35 := stage_O3_O4_O5_commutative_dewitt_sum_and_difference_separation xk yk
  have hO6 := stage_O6_diquark_hodge_dual_and_amari_chentsov_cubic_baryon_tensor u v u xk yk zk 0 0 0
  have hO7 := stage_O7_noncommutative_nambu_associator_on_dewitt_difference u v
  exact ⟨⟨SplitOctonionIsotropicAmariStage.causalEdge_acyclic,
          AmariDuallyFlatOperatorStage.causalEdge_acyclic,
          FirstQuantizedAmariStage.causalEdge_acyclic⟩,
    ⟨hR0.2.2.2.1, hR0.2.2.2.2.1⟩,
    ⟨hO12.2.1.2.2.2.2.2.2.1, hO12.2.2.1⟩,
    ⟨hO35.2.1, hO35.2.2.1, hO35.2.2.2.1, hO35.2.2.2.2.1⟩,
    ⟨hO6.1.1, hO6.2.2.2.1, hO7.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset
