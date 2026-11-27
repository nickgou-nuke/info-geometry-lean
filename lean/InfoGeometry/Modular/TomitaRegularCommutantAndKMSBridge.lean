/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.ComplexMatrixTomitaDuality
import InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality
import InfoGeometry.Algebra.AssociativeRegularCommutant
import InfoGeometry.Modular.TomitaCommutantDuality
import InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS
import InfoGeometry.Modular.RieffelVanDaeleBoundedTomita
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Full Regular-Representation Commutant, Analytic KMS, & TT-F1A Real-Subspace Bridge (`TT-F2`)

This module implements the Milestone `M6` (`TT-F2`) unification across finite-stage
complex matrix Tomita–Takesaki duality, the infinite-stage finite-seed analytic KMS
construction, and the bounded Rieffel–van Daele real-subspace theory (`TT-F1A`):

1. **Full Regular-Representation Commutant Unification (`F13a`):**
   Unifies `InfoGeometry.Modular.ComplexMatrixTomitaDuality`,
   `InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality`,
   `InfoGeometry.Algebra.AssociativeRegularCommutant`, and
   `InfoGeometry.Modular.TomitaCommutantDuality`.
   *Note on missing legacy path:* `InfoGeometry.Canonical.MatrixRegularRepresentationCommutant`
   is intentionally **not** imported because `lean/InfoGeometry/Canonical/MatrixRegularRepresentationCommutant.lean`
   is absent from disk and git history (only orphan `.olean` artifacts remain), so
   importing it would break `lake build`.
   *Note on carrier separation:* `InfoGeometry.Canonical.FiniteMatrixTomitaPolar` is
   strictly excluded so real `Matrix (Fin n) (Fin n) ℝ` (`Xᵀ`) remains separated from
   complex `M_n(ℂ)` and `C⋆`-GNS carriers.

2. **Adversarial Single-Operator Counterexample (`n = 2`) & OpenGauss T16 Witness (`F13b`):**
   Exhibits explicit `2 × 2` complex matrix units `witnessE01`, `witnessE10` proving
   `witnessE01 * witnessE10 ≠ witnessE10 * witnessE01`,
   `leftMul 2 witnessE01 ∈ commutant {leftMul 2 witnessE01} ∧ leftMul 2 witnessE01 ∉ rightRegSet 2`,
   `commutant {leftMul 2 witnessE01} ≠ rightRegSet 2`, and
   `commutant {leftMul 2 (1 : Matrix (Fin 2) (Fin 2) ℂ)} ≠ rightRegSet 2`.

3. **Analytic-KMS Bridge (`F13c`):**
   Constructs `gibbsDensityFactor (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)`
   in `PositiveComplexDensityFactor (2 ^ k)`, proves `modularOp` agrees with
   `gibbsImaginaryTimeAlgEquiv H hH β`, connects `FiniteSeedRepresentedAnalyticKMS.seedFunctional`
   on `seedStageHom H hH β` to `gibbsFunctional H hH β` and `ComplexMatrixTomitaDuality.state`,
   and packages stage-`k` Tomita duality + Gibbs polar factor + `seedFunctional_twisted` +
   `finiteSeedKMSState` into `StageKTomitaAndKMSBridge`.
   *Boundary note:* `matrixFunctionalTwisted` in generic `FilteredGNSMatrixAnalyticKMS`
   remains explicitly preserved for arbitrary compatible state families, and finite-stage
   `commutant (leftRegSet (2 ^ k)) = JConjugateSet (matrixJ (2 ^ k)) (leftRegSet (2 ^ k))`
   is strictly distinct from infinite-dimensional von Neumann commutant duality on
   `representedCStarClosure`.

4. **Bounded Real-Subspace Commutant Criterion (`F14`, Bridge to `TT-F1A`):**
   Proves `bounded_commutant_criterion_of_preserves_subspace` (and `rvdRComplexCLM`
   commutation plus the bidirectional equivalence `commutes_rvdR_and_rvdT_iff_preserves_subspace`),
   keeping `InnerProductSpace.rclikeToReal ℂ H` strictly local (`let` / `letI`) for zero
   `PiLp` / `EuclideanSpace` typeclass diamonds, with two concrete instantiations:
   - `EuclideanSpace ℂ (Fin n)` with `realVecSubmodule n`, and
   - Hilbert–Schmidt `M_n(ℂ)` via `toHS : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin n)`
     with `tomitaRealSubspace F` and a concrete non-orthogonal `n = 2` diagonal witness.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Modular.TomitaRegularCommutantAndKMSBridge

open Matrix Complex
open scoped BigOperators InnerProductSpace
open InfoGeometry.Modular.TomitaCommutantDuality
open InfoGeometry.Modular.TomitaChiralJ
open InfoGeometry.Modular.ComplexMatrixTomitaDuality
open InfoGeometry.Modular.RieffelVanDaeleBoundedTomita
open InfoGeometry.Canonical.RealTomitaStandardSubspace
open InfoGeometry.Algebra.AssociativeRegularCommutant

/-! =========================================================================
    1. Full Regular-Representation Commutant Unification (`F13a`)
    ========================================================================= -/

section CommutantUnification

/-- Full left regular-representation commutant theorem on `M_n(ℂ)`:
`{L_A | A ∈ M_n(ℂ)}' = {R_B | B ∈ M_n(ℂ)}`. -/
theorem fullLeftReg_commutant_eq_rightReg (n : ℕ) :
    commutant (ComplexMatrixTomitaDuality.leftRegSet n) =
      ComplexMatrixTomitaDuality.rightRegSet n :=
  ComplexMatrixTomitaDuality.leftReg_commutant_eq_rightReg n

/-- Full right regular-representation commutant theorem on `M_n(ℂ)`:
`{R_B | B ∈ M_n(ℂ)}' = {L_A | A ∈ M_n(ℂ)}`. -/
theorem fullRightReg_commutant_eq_leftReg (n : ℕ) :
    commutant (ComplexMatrixTomitaDuality.rightRegSet n) =
      ComplexMatrixTomitaDuality.leftRegSet n :=
  ComplexMatrixTomitaDuality.rightReg_commutant_eq_leftReg n

/-- Unconditional `TomitaDualityData` witness for the full left regular representation. -/
theorem fullLeftReg_tomitaDualityData (n : ℕ) :
    TomitaDualityData (ComplexMatrixTomitaDuality.matrixJ n)
      (ComplexMatrixTomitaDuality.leftRegSet n) :=
  ComplexMatrixTomitaDuality.complexMatrixTomitaDualityData n

/-- Tomita–Takesaki commutant duality `L(M_n)' = J L(M_n) J`. -/
theorem fullLeftReg_commutant_eq_JConjugate (n : ℕ) :
    commutant (ComplexMatrixTomitaDuality.leftRegSet n) =
      JConjugateSet (ComplexMatrixTomitaDuality.matrixJ n)
        (ComplexMatrixTomitaDuality.leftRegSet n) :=
  ComplexMatrixTomitaDuality.complexMatrix_commutant_eq_JConjugate n

/-- Von Neumann bicommutant theorem `L(M_n)'' = L(M_n)`. -/
theorem fullLeftReg_bicommutant_eq_self (n : ℕ) :
    commutant (commutant (ComplexMatrixTomitaDuality.leftRegSet n)) =
      ComplexMatrixTomitaDuality.leftRegSet n :=
  ComplexMatrixTomitaDuality.complexMatrix_bicommutant_eq_self n

/-- Definitional compatibility of `leftMulC` and `leftMul`. -/
theorem compat_leftMul (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.leftMulC A :
        Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      ComplexMatrixTomitaDuality.leftMul n A :=
  rfl

/-- Definitional compatibility of `rightMulC` and `rightMul`. -/
theorem compat_rightMul (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.rightMulC B :
        Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      ComplexMatrixTomitaDuality.rightMul n B :=
  rfl

/-- Definitional compatibility of `ComplexMatrixTomitaCommutantDuality.leftRegSet` and
`ComplexMatrixTomitaDuality.leftRegSet`. -/
theorem compat_leftRegSet (n : ℕ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.leftRegSet n =
      ComplexMatrixTomitaDuality.leftRegSet n :=
  rfl

/-- Definitional compatibility of `ComplexMatrixTomitaCommutantDuality.rightRegSet` and
`ComplexMatrixTomitaDuality.rightRegSet`. -/
theorem compat_rightRegSet (n : ℕ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.rightRegSet n =
      ComplexMatrixTomitaDuality.rightRegSet n :=
  rfl

/-- Definitional compatibility of `modularConjInvolution` and `matrixJ`. -/
theorem compat_modularConjInvolution (n : ℕ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.modularConjInvolution n =
      ComplexMatrixTomitaDuality.matrixJ n :=
  rfl

/-- Definitional compatibility of `hsInnerC` and `hsInner`. -/
theorem compat_hsInner (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.hsInnerC X Y =
      ComplexMatrixTomitaDuality.hsInner n X Y :=
  rfl

/-- Convert a canonical `PositiveComplexDensityFactor` to the modular owner type. -/
def toModularDensityFactor {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n) :
    ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n where
  r := F.r
  rInv := F.rInv
  r_herm := F.r_herm
  rInv_herm := F.rInv_herm
  r_mul_rInv := F.r_mul_rInv
  rInv_mul_r := F.rInv_mul_r

/-- Convert a modular `PositiveComplexDensityFactor` to the canonical owner type. -/
def ofModularDensityFactor {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n where
  r := F.r
  rInv := F.rInv
  r_herm := F.r_herm
  rInv_herm := F.rInv_herm
  r_mul_rInv := F.r_mul_rInv
  rInv_mul_r := F.rInv_mul_r

@[simp]
theorem toModularDensityFactor_ofModular {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    toModularDensityFactor (ofModularDensityFactor F) = F := by
  cases F
  rfl

@[simp]
theorem ofModularDensityFactor_toModular {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n) :
    ofModularDensityFactor (toModularDensityFactor F) = F := by
  cases F
  rfl

theorem compat_tomitaOpC_eq_tomitaOp {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.tomitaOpC F X =
      ComplexMatrixTomitaDuality.tomitaOp (toModularDensityFactor F) X :=
  rfl

theorem compat_modularOpC_eq_modularOp {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.modularOpC F X =
      ComplexMatrixTomitaDuality.modularOp (toModularDensityFactor F) X :=
  rfl

theorem compat_modularSqrtC_eq_modularSqrt {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.modularSqrtC F X =
      ComplexMatrixTomitaDuality.modularSqrt (toModularDensityFactor F) X :=
  rfl

theorem compat_state_eq_trace {n : ℕ}
    (F : InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (F.rho * X).trace =
      ComplexMatrixTomitaDuality.state (toModularDensityFactor F) X :=
  rfl

/-- `AssociativeRegularCommutant.leftRegular` coerces to `ComplexMatrixTomitaDuality.leftMul`. -/
theorem leftRegular_coe_eq_leftMul (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ⇑(leftRegular (R := ℂ) A) = ComplexMatrixTomitaDuality.leftMul n A :=
  rfl

/-- `AssociativeRegularCommutant.rightRegular` coerces to `ComplexMatrixTomitaDuality.rightMul`. -/
theorem rightRegular_coe_eq_rightMul (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ⇑(rightRegular (R := ℂ) B) = ComplexMatrixTomitaDuality.rightMul n B :=
  rfl

/-- Equivalence between commuting with `leftRegSet n` as a set function and belonging to
`AssociativeRegularCommutant.leftRegularCommutant` on `Module.End ℂ (Matrix (Fin n) (Fin n) ℂ)`. -/
theorem linearMap_mem_commutant_leftRegSet_iff (n : ℕ)
    (T : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    (T : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) ∈
        commutant (ComplexMatrixTomitaDuality.leftRegSet n) ↔
      T ∈ leftRegularCommutant (R := ℂ) (A := Matrix (Fin n) (Fin n) ℂ) := by
  constructor
  · intro hT a x
    exact hT (ComplexMatrixTomitaDuality.leftMul n a) ⟨a, rfl⟩ x
  · rintro hT _ ⟨a, rfl⟩ x
    exact hT a x

/-- Bridge equating the linear commutant of `leftRegSet n` with the range of
`AssociativeRegularCommutant.rightRegular` via `leftRegularCommutant_eq_rightRegular_range`. -/
theorem linearMap_mem_commutant_leftRegSet_iff_rightRegular (n : ℕ)
    (T : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    (T : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) ∈
        commutant (ComplexMatrixTomitaDuality.leftRegSet n) ↔
      ∃ B : Matrix (Fin n) (Fin n) ℂ, T = rightRegular (R := ℂ) B := by
  rw [linearMap_mem_commutant_leftRegSet_iff, leftRegularCommutant_eq_rightRegular_range]
  rfl

end CommutantUnification

/-! =========================================================================
    2. Adversarial Single-Operator Counterexample (`n = 2`) & T16 Witness (`F13b`)
    ========================================================================= -/

section SingleOperatorCounterexample

/-- Any single left multiplication `L_A` trivially lies in its own commutant `{L_A}'`. -/
theorem leftMul_mem_single_commutant (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ComplexMatrixTomitaDuality.leftMul n A ∈
      commutant {ComplexMatrixTomitaDuality.leftMul n A} := by
  rintro _ rfl _
  rfl

/-- If `A` fails to commute with some `X`, then `L_A ∉ {R_B | B ∈ M_n(ℂ)}`. -/
theorem leftMul_not_mem_rightRegSet_of_noncomm {n : ℕ}
    {A X : Matrix (Fin n) (Fin n) ℂ} (h : A * X ≠ X * A) :
    ComplexMatrixTomitaDuality.leftMul n A ∉ ComplexMatrixTomitaDuality.rightRegSet n := by
  rintro ⟨B, hB⟩
  have h1 := congrArg (fun f => f 1) hB
  simp only [ComplexMatrixTomitaDuality.leftMul, ComplexMatrixTomitaDuality.rightMul,
    Matrix.mul_one, Matrix.one_mul] at h1
  subst h1
  have hX := congrArg (fun f => f X) hB
  simp only [ComplexMatrixTomitaDuality.leftMul, ComplexMatrixTomitaDuality.rightMul] at hX
  exact h hX

/-- Explicit `2 × 2` nilpotent matrix unit `E₀₁`. -/
def witnessE01 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 1], ![0, 0]]

/-- Explicit `2 × 2` nilpotent matrix unit `E₁₀`. -/
def witnessE10 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 0], ![1, 0]]

/-- Explicit noncommuting product `E₀₁ * E₁₀ ≠ E₁₀ * E₀₁`. -/
theorem witnessE01_mul_witnessE10_ne :
    witnessE01 * witnessE10 ≠ witnessE10 * witnessE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have hL : (witnessE01 * witnessE10) 0 0 = 1 := by
    simp [witnessE01, witnessE10, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (witnessE10 * witnessE01) 0 0 = 0 := by
    simp [witnessE01, witnessE10, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h00
  exact one_ne_zero h00

/-- Closed OpenGauss T16 noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨witnessE01, witnessE10, witnessE01_mul_witnessE10_ne⟩

/-- `L_{E₀₁}` belongs to `{L_{E₀₁}}'` yet does not lie in `{R_B | B ∈ M₂(ℂ)}`. -/
theorem single_leftMul_mem_commutant_not_rightRegSet :
    ComplexMatrixTomitaDuality.leftMul 2 witnessE01 ∈
        commutant {ComplexMatrixTomitaDuality.leftMul 2 witnessE01} ∧
      ComplexMatrixTomitaDuality.leftMul 2 witnessE01 ∉
        ComplexMatrixTomitaDuality.rightRegSet 2 :=
  ⟨leftMul_mem_single_commutant 2 witnessE01,
    leftMul_not_mem_rightRegSet_of_noncomm witnessE01_mul_witnessE10_ne⟩

/-- Adversarial separation: for the singleton `{L_{E₀₁}}`, `{L_{E₀₁}}' ≠ rightRegSet 2`. -/
theorem single_leftMul_commutant_ne_rightRegSet :
    commutant {ComplexMatrixTomitaDuality.leftMul 2 witnessE01} ≠
      ComplexMatrixTomitaDuality.rightRegSet 2 := by
  intro hEq
  have hmem := single_leftMul_mem_commutant_not_rightRegSet.1
  rw [hEq] at hmem
  exact single_leftMul_mem_commutant_not_rightRegSet.2 hmem

/-- Adversarial separation for the identity singleton `{L_1}`: `{L_1}' ≠ rightRegSet 2`,
witnessed by `L_{E₀₁} ∈ {L_1}' \ rightRegSet 2`. -/
theorem single_leftMul_one_commutant_ne_rightRegSet :
    commutant {ComplexMatrixTomitaDuality.leftMul 2 (1 : Matrix (Fin 2) (Fin 2) ℂ)} ≠
      ComplexMatrixTomitaDuality.rightRegSet 2 := by
  intro hEq
  have hcomm : ComplexMatrixTomitaDuality.leftMul 2 witnessE01 ∈
      commutant {ComplexMatrixTomitaDuality.leftMul 2 (1 : Matrix (Fin 2) (Fin 2) ℂ)} := by
    rintro _ rfl X
    simp [ComplexMatrixTomitaDuality.leftMul]
  rw [hEq] at hcomm
  exact single_leftMul_mem_commutant_not_rightRegSet.2 hcomm

end SingleOperatorCounterexample

/-! =========================================================================
    3. Analytic-KMS Bridge (`F13c`)
    ========================================================================= -/

section AnalyticKMSBridge

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.FiniteSeedRepresentedKMS
open InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
open InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumReadback
open CStarStateColimit.Native.FilteredGNSVacuumState
open CStarStateColimit.Native.FilteredGNSMatrixAnalyticKMS
open scoped ComplexOrder

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

private lemma expWeight_mul {a b : ℝ} :
    expWeight a * expWeight b = expWeight (a + b) := by
  funext r
  simp only [Pi.mul_apply, expWeight, ← Real.exp_add]
  ring_nf

private lemma gibbsDensity_mul_gibbsDensity {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (a b : ℝ) :
    gibbsDensity H hH a * gibbsDensity H hH b = gibbsDensity H hH (a + b) := by
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  have ha : ContinuousOn (expWeight a) (spectrum ℝ H) := by
    unfold expWeight
    fun_prop
  have hb : ContinuousOn (expWeight b) (spectrum ℝ H) := by
    unfold expWeight
    fun_prop
  rw [gibbsDensity, gibbsDensity, gibbsDensity, ← hH.cfc_eq, ← hH.cfc_eq, ← hH.cfc_eq]
  rw [← cfc_mul (expWeight a) (expWeight b) H ha hb]
  congr 1
  exact expWeight_mul

private lemma gibbsDensity_zero {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    gibbsDensity H hH 0 = 1 := by
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  rw [gibbsDensity, ← hH.cfc_eq]
  have hfun : expWeight 0 = (1 : ℝ → ℝ) := by
    funext r
    simp [expWeight]
  rw [hfun]
  exact cfc_one ℝ H

/-- Stage-`k` Gibbs density factor `r = gibbsDensity H hH (β / 2)` and
`rInv = gibbsDensity H hH (-(β / 2))` in `PositiveComplexDensityFactor (2 ^ k)`. -/
def gibbsDensityFactor {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    ComplexMatrixTomitaDuality.PositiveComplexDensityFactor (2 ^ k) where
  r := gibbsDensity H hH (β / 2)
  rInv := gibbsDensity H hH (-(β / 2))
  r_herm := gibbsDensity_isHermitian H hH (β / 2)
  rInv_herm := gibbsDensity_isHermitian H hH (-(β / 2))
  r_mul_rInv := by
    rw [gibbsDensity_mul_gibbsDensity, add_neg_cancel]
    exact gibbsDensity_zero H hH
  rInv_mul_r := by
    rw [gibbsDensity_mul_gibbsDensity, neg_add_cancel]
    exact gibbsDensity_zero H hH

@[simp]
theorem gibbsDensityFactor_rho {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsDensityFactor H hH β).rho = gibbsDensity H hH β := by
  change gibbsDensity H hH (β / 2) * gibbsDensity H hH (β / 2) = gibbsDensity H hH β
  rw [gibbsDensity_mul_gibbsDensity]
  ring_nf

@[simp]
theorem gibbsDensityFactor_rhoInv {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsDensityFactor H hH β).rhoInv = gibbsDensity H hH (-β) := by
  change gibbsDensity H hH (-(β / 2)) * gibbsDensity H hH (-(β / 2)) = gibbsDensity H hH (-β)
  rw [gibbsDensity_mul_gibbsDensity]
  ring_nf

private lemma gibbsDensityUnit_inv_coe {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (((gibbsDensityUnit H hH β)⁻¹ : (MatrixStage k)ˣ) : MatrixStage k) = gibbsDensity H hH (-β) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [gibbsDensityUnit_coe, gibbsDensity_mul_gibbsDensity, add_neg_cancel]
  exact gibbsDensity_zero H hH

/-- The stage-`k` modular operator `modularOp (gibbsDensityFactor H hH β)` coincides
exactly with `gibbsImaginaryTimeAlgEquiv H hH β`. -/
theorem gibbsDensityFactor_modularOp_eq {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian)
    (β : ℝ) (X : MatrixStage k) :
    ComplexMatrixTomitaDuality.modularOp (gibbsDensityFactor H hH β) X =
      gibbsImaginaryTimeAlgEquiv H hH β X := by
  rw [ComplexMatrixTomitaDuality.modularOp, gibbsDensityFactor_rho, gibbsDensityFactor_rhoInv,
    gibbsImaginaryTimeAlgEquiv_apply, gibbsDensityUnit_inv_coe]

section GenericStageReadback

universe u

private lemma representedMatrixStageMap_vacuum_eq
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    (i v : I) (e : Matrix n n ℂ →⋆ₐ[ℂ] Stage i) (X : Matrix n n ℂ) :
    representedVacuumFunctional Stage sys ω v
        (FilteredGNSMatrixRealTime.representedMatrixStageMap Stage sys ω i e X) =
      (ω.state i).functional (e X) := by
  dsimp only [FilteredGNSMatrixRealTime.representedMatrixStageMap,
    StarAlgHom.comp_apply]
  have hj : algebraicColimitToRepresentedClosure Stage sys ω
      (algebraicStarDirectLimitOf Stage sys i (e X)) =
      ⟨FilteredGNSGlobalStageRepresentation.globalStageRepresentationStarAlgHom
          Stage sys ω i (e X),
        globalStageRepresentation_mem_representedCStarClosure
          Stage sys ω i (e X)⟩ := by
    apply Subtype.ext
    exact FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation_of
      Stage sys ω i (e X)
  rw [hj]
  exact representedVacuumFunctional_stage Stage sys ω v i (e X)

end GenericStageReadback

private lemma seedFunctional_stage_readback_bridge {k : ℕ} (H : MatrixStage k)
    (hH : H.IsHermitian) (β : ℝ) (v : ℕ) (X : MatrixStage k) :
    seedFunctional H hH β v (seedStageHom H hH β X) =
      representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) v
        (FilteredGNSMatrixRealTime.representedMatrixStageMap CStarMatrixStage
          cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β) k
          (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom
          X) := by
  have hf : seedFunctional H hH β v =
      representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) v := rfl
  have hx_hom : seedStageHom H hH β =
      FilteredGNSMatrixRealTime.representedMatrixStageMap CStarMatrixStage
        cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β) k
        (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom :=
    rfl
  exact DFunLike.congr hf (DFunLike.congr hx_hom rfl)

/-- On stage `k`, `FiniteSeedRepresentedAnalyticKMS.seedFunctional` evaluated on
`seedStageHom H hH β X` equals `gibbsFunctional H hH β X`. -/
theorem seedFunctional_stage_eq_gibbsFunctional {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian)
    (β : ℝ) (v : ℕ) (X : MatrixStage k) :
    seedFunctional H hH β v (seedStageHom H hH β X) = gibbsFunctional H hH β X := by
  have h1 := seedFunctional_stage_readback_bridge H hH β v X
  have hgen := representedMatrixStageMap_vacuum_eq CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β) k v
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom X
  have h2 :
      ((finiteSeedCompatibleStageStates H hH β).state k).functional
          ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom
            X) =
        gibbsFunctional H hH β X := by
    change (finiteSeedStageState H hH β k).functional (CStarMatrix.ofMatrixStarAlgEquiv X) = _
    rw [finiteSeedStageState_apply]
    simp only [StarAlgEquiv.symm_apply_apply]
    exact normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional H hH β X
  exact h1.trans (hgen.trans h2)

/-- On stage `k`, `seedFunctional` equals the normalized `ComplexMatrixTomitaDuality.state`
associated with `gibbsDensityFactor H hH β`. -/
theorem seedFunctional_stage_eq_normalized_tomitaState {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (v : ℕ) (X : MatrixStage k) :
    seedFunctional H hH β v (seedStageHom H hH β X) =
      (Matrix.trace (gibbsDensityFactor H hH β).rho)⁻¹ *
        ComplexMatrixTomitaDuality.state (gibbsDensityFactor H hH β) X := by
  rw [seedFunctional_stage_eq_gibbsFunctional, gibbsFunctional_apply, ← gibbsDensityFactor_rho]
  rfl

/-- Exact stage-`k` algebraic KMS identity connecting `seedFunctional` and
`ComplexMatrixTomitaDuality.modularOp (gibbsDensityFactor H hH β)`. -/
theorem seedFunctional_stage_modularOp_kms {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (v : ℕ) (X Y : MatrixStage k) :
    seedFunctional H hH β v
        (seedStageHom H hH β
          (X * ComplexMatrixTomitaDuality.modularOp (gibbsDensityFactor H hH β) Y)) =
      seedFunctional H hH β v (seedStageHom H hH β (Y * X)) :=
  (seedFunctional_stage_eq_normalized_tomitaState H hH β v
      (X * ComplexMatrixTomitaDuality.modularOp (gibbsDensityFactor H hH β) Y)).trans
    ((congrArg (fun z => (Matrix.trace (gibbsDensityFactor H hH β).rho)⁻¹ * z)
        (ComplexMatrixTomitaDuality.modularOp_kms_identity (gibbsDensityFactor H hH β) X Y)).trans
      (seedFunctional_stage_eq_normalized_tomitaState H hH β v (Y * X)).symm)

set_option maxHeartbeats 2500000 in
/-- Cohesive stage-`k` bridge packaging algebraic finite-stage Tomita duality, the Gibbs
polar density factor, the `modularOp = gibbsImaginaryTimeAlgEquiv` identification, and
the completed analytic KMS state `finiteSeedKMSState` (which discharges
`FilteredGNSMatrixAnalyticKMS.matrixFunctionalTwisted` via
`FiniteSeedRepresentedAnalyticKMS.seedFunctional_twisted` to prove `upper_boundary`).

*Scope boundary:* This bridge leaves `matrixFunctionalTwisted` intact in generic
`FilteredGNSMatrixAnalyticKMS` (for arbitrary state families) and does **not** conflate
finite-stage `commutant (leftRegSet (2 ^ k)) = JConjugateSet (matrixJ (2 ^ k)) (leftRegSet (2 ^ k))`
with infinite-dimensional von Neumann commutant duality on `representedCStarClosure`. -/
structure StageKTomitaAndKMSBridge {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian)
    (β : ℝ) (hβ : 0 < β) (v : ℕ) where
  densityFactor : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor (2 ^ k)
  dualityData :
    TomitaDualityData (ComplexMatrixTomitaDuality.matrixJ (2 ^ k))
      (ComplexMatrixTomitaDuality.leftRegSet (2 ^ k))
  modularData : TomitaModularData (MatrixStage k)
  modularOp_eq :
    ∀ X : MatrixStage k,
      ComplexMatrixTomitaDuality.modularOp densityFactor X =
        gibbsImaginaryTimeAlgEquiv H hH β X
  kmsState :
    InfoGeometry.Geometry.IsKMSState
      (fun t => (seedRealTimeAut H hH β t).toAlgEquiv) β

set_option maxHeartbeats 2500000 in
/-- Constructive inhabitant of `StageKTomitaAndKMSBridge` for any Hermitian stage-`k`
Hamiltonian `H` and inverse temperature `β > 0`. -/
def stageKTomitaAndKMSBridge {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian)
    (β : ℝ) (hβ : 0 < β) (v : ℕ) : StageKTomitaAndKMSBridge H hH β hβ v where
  densityFactor := gibbsDensityFactor H hH β
  dualityData := ComplexMatrixTomitaDuality.complexMatrixTomitaDualityData (2 ^ k)
  modularData :=
    ComplexMatrixTomitaDuality.complexMatrixTomitaModularData (gibbsDensityFactor H hH β)
  modularOp_eq := gibbsDensityFactor_modularOp_eq H hH β
  kmsState := finiteSeedKMSState H hH β hβ v

/-- Concrete non-scalar Hermitian stage-`1` Pauli-Z Hamiltonian `diag(1, -1)`. -/
def diagPauliZStage1 : MatrixStage 1 :=
  Matrix.diagonal ![(1 : ℂ), -1]

theorem diagPauliZStage1_isHermitian : diagPauliZStage1.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagPauliZStage1, Matrix.conjTranspose_apply]

/-- Closed constructive witness inhabiting `StageKTomitaAndKMSBridge` on stage `1` at `β = 1`. -/
def stage1DiagTomitaAndKMSBridge :
    StageKTomitaAndKMSBridge diagPauliZStage1 diagPauliZStage1_isHermitian 1 zero_lt_one 0 :=
  stageKTomitaAndKMSBridge diagPauliZStage1 diagPauliZStage1_isHermitian 1 zero_lt_one 0

end AnalyticKMSBridge

/-! =========================================================================
    4. Bounded Real-Subspace Commutant Criterion (`F14`, Bridge to `TT-F1A`)
    ========================================================================= -/

section BoundedRealSubspaceBridge

/-- Under the local realification `InnerProductSpace.rclikeToReal ℂ H`, the real
adjoint of `A.restrictScalars ℝ` coincides with `(A.adjoint).restrictScalars ℝ`. -/
theorem restrictScalars_adjoint_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    (A.restrictScalars ℝ).adjoint = A.adjoint.restrictScalars ℝ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change (⟪A.adjoint x, y⟫_ℂ).re = (⟪x, A y⟫_ℂ).re
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- If an `ℝ`-continuous linear map `B` and its adjoint `B.adjoint` both preserve a
complete real subspace `M`, then `B` commutes with `M.starProjection`. -/
theorem commute_starProjection_of_preserves {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (M : Submodule ℝ E) [CompleteSpace M]
    (B : E →L[ℝ] E) (hB : ∀ x ∈ M, B x ∈ M) (hBAdj : ∀ x ∈ M, B.adjoint x ∈ M) :
    B.comp M.starProjection = M.starProjection.comp B := by
  ext x
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hB _ (M.starProjection_apply_mem x)) fun w hw => ?_
  change ⟪B x - B (M.starProjection x), w⟫_ℝ = 0
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact M.starProjection_inner_eq_zero x (B.adjoint w) (hBAdj w hw)

/-- Any `ℂ`-continuous linear map preserving `K` automatically preserves
`ImaginarySubmodule K = i K`. -/
theorem preserves_imaginarySubmodule_of_clm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Submodule ℝ H} (A : H →L[ℂ] H)
    (hAK : ∀ x ∈ K, A x ∈ K) :
    ∀ x ∈ ImaginarySubmodule (H := H) K, A x ∈ ImaginarySubmodule (H := H) K := by
  intro x hx
  rw [mem_imaginarySubmodule_iff] at hx ⊢
  rw [← A.map_smul]
  exact hAK _ hx

/-- `A.restrictScalars ℝ` commutes with `projK K` when `A` and `A.adjoint` preserve `K`. -/
theorem commutes_projK_of_preserves_subspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (A.restrictScalars ℝ).comp (projK (H := H) K) =
      (projK (H := H) K).comp (A.restrictScalars ℝ) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  refine commute_starProjection_of_preserves K (A.restrictScalars ℝ) hAK ?_
  intro x hx
  rw [restrictScalars_adjoint_eq]
  exact hAdjK x hx

/-- `A.restrictScalars ℝ` commutes with `projIK K` when `A` and `A.adjoint` preserve `K`. -/
theorem commutes_projIK_of_preserves_subspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (A.restrictScalars ℝ).comp (projIK (H := H) K) =
      (projIK (H := H) K).comp (A.restrictScalars ℝ) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  refine commute_starProjection_of_preserves (ImaginarySubmodule (H := H) K)
    (A.restrictScalars ℝ)
    (preserves_imaginarySubmodule_of_clm A hAK) ?_
  intro x hx
  rw [restrictScalars_adjoint_eq]
  exact preserves_imaginarySubmodule_of_clm A.adjoint hAdjK x hx

/-- **Bounded Real-Subspace Commutant Criterion (`TT-F1A` Bridge):**
If `A : H →L[ℂ] H` and `A.adjoint` preserve a closed real subspace `K : Submodule ℝ H`,
then `A.restrictScalars ℝ` commutes with `projK K`, `projIK K`, `rvdR K`, and `rvdT K`. -/
theorem bounded_commutant_criterion_of_preserves_subspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (A.restrictScalars ℝ).comp (projK (H := H) K) =
        (projK (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (projIK (H := H) K) =
        (projIK (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (rvdR (H := H) K) =
        (rvdR (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (rvdT (H := H) K) =
        (rvdT (H := H) K).comp (A.restrictScalars ℝ) := by
  have hP := commutes_projK_of_preserves_subspace K A hAK hAdjK
  have hQ := commutes_projIK_of_preserves_subspace K A hAK hAdjK
  refine ⟨hP, hQ, ?_, ?_⟩
  · simp only [rvdR, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, hP, hQ]
  · simp only [rvdT, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hP, hQ]

/-- Complex-linear commutation with `rvdRComplexCLM K` when `A` and `A.adjoint` preserve `K`. -/
theorem commutes_rvdRComplexCLM_of_preserves_subspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    A.comp (rvdRComplexCLM (H := H) K) = (rvdRComplexCLM (H := H) K).comp A := by
  have hR := (bounded_commutant_criterion_of_preserves_subspace K A hAK hAdjK).2.2.1
  ext x
  exact congrArg (fun f : H →L[ℝ] H => f x) hR

/-- Bidirectional characterization: `A.restrictScalars ℝ` commutes with both `rvdR K` and
`rvdT K` if and only if both `A` and `A.adjoint` preserve `K`. -/
theorem commutes_rvdR_and_rvdT_iff_preserves_subspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (A : H →L[ℂ] H) :
    ((A.restrictScalars ℝ).comp (rvdR (H := H) K) =
        (rvdR (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (rvdT (H := H) K) =
        (rvdT (H := H) K).comp (A.restrictScalars ℝ)) ↔
      ((∀ x ∈ K, A x ∈ K) ∧ (∀ x ∈ K, A.adjoint x ∈ K)) := by
  constructor
  · rintro ⟨hR, hT⟩
    have hprojK : (A.restrictScalars ℝ).comp (projK (H := H) K) =
        (projK (H := H) K).comp (A.restrictScalars ℝ) := by
      ext x
      have hRx := congrArg (fun f : H →L[ℝ] H => f x) hR
      have hTx := congrArg (fun f : H →L[ℝ] H => f x) hT
      have hadd := congrArg₂ (· + ·) hRx hTx
      have hsum : ∀ y : H, rvdR (H := H) K y + rvdT (H := H) K y = (2 : ℝ) • projK (H := H) K y := by
        intro y
        simp only [rvdR, rvdT, _root_.add_apply, _root_.sub_apply]
        module
      change A (rvdR (H := H) K x) + A (rvdT (H := H) K x) =
        rvdR (H := H) K (A x) + rvdT (H := H) K (A x) at hadd
      have hA2 : A ((2 : ℝ) • projK (H := H) K x) = (2 : ℝ) • A (projK (H := H) K x) :=
        (A.restrictScalars ℝ).map_smul (2 : ℝ) (projK (H := H) K x)
      rw [← map_add A, hsum x, hsum (A x), hA2] at hadd
      exact smul_right_injective H (by norm_num : (2 : ℝ) ≠ 0) hadd
    refine ⟨?_, ?_⟩
    · intro x hx
      have hAx : A x = projK (H := H) K (A x) := by
        have h := congrArg (fun f : H →L[ℝ] H => f x) hprojK
        change A (projK (H := H) K x) = projK (H := H) K (A x) at h
        rwa [(projK_eq_self_iff K x).mpr hx] at h
      rw [hAx]
      exact projK_apply_mem K (A x)
    · intro x hx
      let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      have hinner : ∀ w : H, ⟪A.adjoint x, w⟫_ℝ = ⟪projK (H := H) K (A.adjoint x), w⟫_ℝ := by
        intro w
        have hPself := projK_isSelfAdjoint (H := H) K
        have hcomm_w : A (projK (H := H) K w) = projK (H := H) K (A w) :=
          congrArg (fun f : H →L[ℝ] H => f w) hprojK
        calc
          ⟪A.adjoint x, w⟫_ℝ = (⟪A.adjoint x, w⟫_ℂ).re := rfl
          _ = (⟪x, A w⟫_ℂ).re := by rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪x, A w⟫_ℝ := rfl
          _ = ⟪projK (H := H) K x, A w⟫_ℝ := by rw [(projK_eq_self_iff K x).mpr hx]
          _ = ⟪x, projK (H := H) K (A w)⟫_ℝ :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPself x (A w)
          _ = ⟪x, A (projK (H := H) K w)⟫_ℝ := by rw [← hcomm_w]
          _ = (⟪x, A (projK (H := H) K w)⟫_ℂ).re := rfl
          _ = (⟪A.adjoint x, projK (H := H) K w⟫_ℂ).re := by
            rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪A.adjoint x, projK (H := H) K w⟫_ℝ := rfl
          _ = ⟪projK (H := H) K (A.adjoint x), w⟫_ℝ :=
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPself (A.adjoint x) w).symm
      have heq : A.adjoint x = projK (H := H) K (A.adjoint x) := by
        apply ext_inner_right ℝ
        intro w
        exact hinner w
      rw [heq]
      exact projK_apply_mem K (A.adjoint x)
  · rintro ⟨hAK, hAdjK⟩
    have hcrit := bounded_commutant_criterion_of_preserves_subspace K A hAK hAdjK
    exact ⟨hcrit.2.2.1, hcrit.2.2.2⟩

/-! ### Instantiation 1: `EuclideanSpace ℂ (Fin n)` with `realVecSubmodule n` -/

section EuclideanSpaceInstantiation

/-- Real coordinate subspace `{v | ∀ i, (v i).im = 0}` inside `EuclideanSpace ℂ (Fin n)`. -/
def realVecSubmodule (n : ℕ) : Submodule ℝ (EuclideanSpace ℂ (Fin n)) where
  carrier := {v | ∀ i, (v i).im = 0}
  zero_mem' := fun _ => by simp
  add_mem' := fun {x y} hx hy i => by simp [hx i, hy i]
  smul_mem' := fun c {x} hx i => by
    change (c • x i).im = 0
    simp [Complex.real_smul, hx i]

@[simp]
theorem mem_realVecSubmodule_iff (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    v ∈ realVecSubmodule n ↔ ∀ i, (v i).im = 0 :=
  Iff.rfl

theorem isClosed_realVecSubmodule (n : ℕ) :
    IsClosed (realVecSubmodule n : Set (EuclideanSpace ℂ (Fin n))) :=
  Submodule.closed_of_finiteDimensional (realVecSubmodule n)

instance (n : ℕ) : CompleteSpace (realVecSubmodule n) :=
  (isClosed_realVecSubmodule n).completeSpace_coe

instance (n : ℕ) :
    CompleteSpace (ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) :=
  completeSpace_imaginarySubmodule (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)

theorem realVecSubmodule_isStandard (n : ℕ) :
    IsStandardSubspace (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n) := by
  constructor
  · have htop :
        realVecSubmodule n ⊔
          ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      let vRe : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => ((v i).re : ℂ))
      let vIm : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => ((v i).im : ℂ))
      have hvRe : vRe ∈ realVecSubmodule n := fun i => by simp [vRe]
      have hvIm : (Complex.I : ℂ) • vIm ∈
          ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n) := by
        rw [mem_imaginarySubmodule_iff]
        intro i
        change ((-Complex.I : ℂ) * (Complex.I * ((v i).im : ℂ))).im = 0
        have hI : (-Complex.I : ℂ) * (Complex.I * ((v i).im : ℂ)) = ((v i).im : ℂ) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
        rw [hI]
        simp
      have hv_eq : vRe + (Complex.I : ℂ) • vIm = v := by
        ext i
        change ((v i).re : ℂ) + Complex.I * ((v i).im : ℂ) = v i
        simpa [mul_comm] using Complex.re_add_im (v i)
      rw [Submodule.mem_sup]
      exact ⟨vRe, hvRe, (Complex.I : ℂ) • vIm, hvIm, hv_eq⟩
    rw [htop]
    simp [dense_univ]
  · rw [eq_bot_iff]
    intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨h1, h2⟩
    rw [mem_imaginarySubmodule_iff] at h2
    ext i
    have him : (v i).im = 0 := h1 i
    have hre : (v i).re = 0 := by
      have h2i := h2 i
      change ((-Complex.I : ℂ) * v i).im = 0 at h2i
      simpa [Complex.mul_im] using h2i
    exact Complex.ext hre him

/-- Coordinatewise complex conjugation on `EuclideanSpace ℂ (Fin n)` as a real-linear isometry. -/
def vecConjLIE (n : ℕ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun v := WithLp.toLp 2 (fun i => star (v i))
  invFun v := WithLp.toLp 2 (fun i => star (v i))
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' x y := by ext i; simp
  map_smul' c x := by
    ext i
    change star ((c : ℂ) * x i) = (c : ℂ) * star (x i)
    simp
  norm_map' x := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖star (x i)‖ ^ 2 = ‖x i‖ ^ 2
    rw [norm_star]

/-- Lift any real matrix `M : Matrix (Fin n) (Fin n) ℝ` to a complex CLM on
`EuclideanSpace ℂ (Fin n)` with zero typeclass diamonds. -/
def realMatrixToEuclideanCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (M.map Complex.ofReal).toEuclideanLin.toContinuousLinearMap

theorem realMatrixToEuclideanCLM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    realMatrixToEuclideanCLM M v i = ∑ j : Fin n, (M i j : ℂ) * v j := by
  simp [realMatrixToEuclideanCLM, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct]

theorem realMatrixToEuclideanCLM_adjoint {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (realMatrixToEuclideanCLM M).adjoint = realMatrixToEuclideanCLM Mᵀ := by
  have hconj : (M.map Complex.ofReal)ᴴ = Mᵀ.map Complex.ofReal := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  have hadj := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (M.map Complex.ofReal)
  change ⟪(Mᵀ.map Complex.ofReal).toEuclideanLin u, v⟫_ℂ =
    ⟪u, (M.map Complex.ofReal).toEuclideanLin v⟫_ℂ
  rw [← hconj, hadj, LinearMap.adjoint_inner_left]

theorem realMatrixToEuclideanCLM_preserves {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∀ v ∈ realVecSubmodule n, realMatrixToEuclideanCLM M v ∈ realVecSubmodule n := by
  intro v hv i
  rw [realMatrixToEuclideanCLM_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hvj : (v j).im = 0 := hv j
  simp [Complex.mul_im, hvj]

/-- Any real-entry matrix operator on `EuclideanSpace ℂ (Fin n)` commutes with
`projK`, `projIK`, `rvdR`, and `rvdT` for `realVecSubmodule n`. -/
theorem realMatrixToEuclideanCLM_commutes_rvd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ((realMatrixToEuclideanCLM M).restrictScalars ℝ).comp
          (projK (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) =
        (projK (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)).comp
          ((realMatrixToEuclideanCLM M).restrictScalars ℝ) ∧
      ((realMatrixToEuclideanCLM M).restrictScalars ℝ).comp
          (projIK (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) =
        (projIK (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)).comp
          ((realMatrixToEuclideanCLM M).restrictScalars ℝ) ∧
      ((realMatrixToEuclideanCLM M).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) =
        (rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)).comp
          ((realMatrixToEuclideanCLM M).restrictScalars ℝ) ∧
      ((realMatrixToEuclideanCLM M).restrictScalars ℝ).comp
          (rvdT (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) =
        (rvdT (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)).comp
          ((realMatrixToEuclideanCLM M).restrictScalars ℝ) := by
  refine bounded_commutant_criterion_of_preserves_subspace (realVecSubmodule n)
    (realMatrixToEuclideanCLM M) (realMatrixToEuclideanCLM_preserves M) ?_
  rw [realMatrixToEuclideanCLM_adjoint]
  exact realMatrixToEuclideanCLM_preserves Mᵀ

/-- Concrete `n = 2` real-entry `ℂ`-CLM witness `E₀₁` on `EuclideanSpace ℂ (Fin 2)`. -/
def realVecE01CLM : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  realMatrixToEuclideanCLM (Matrix.of ![![0, (1 : ℝ)], ![0, 0]])

/-- Concrete `n = 2` real-entry `ℂ`-CLM witness `E₁₀` on `EuclideanSpace ℂ (Fin 2)`. -/
def realVecE10CLM : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  realMatrixToEuclideanCLM (Matrix.of ![![0, 0], ![(1 : ℝ), 0]])

/-- `realVecE01CLM` and `realVecE10CLM` do not commute as bounded `ℂ`-linear operators on
`EuclideanSpace ℂ (Fin 2)`. -/
theorem realVecE01CLM_comp_realVecE10CLM_ne :
    realVecE01CLM.comp realVecE10CLM ≠ realVecE10CLM.comp realVecE01CLM := by
  intro h
  let e0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => f e0 0) h
  have hL : (realVecE01CLM.comp realVecE10CLM) e0 0 = 1 := by
    simp [realVecE01CLM, realVecE10CLM, realMatrixToEuclideanCLM_apply, Fin.sum_univ_two, e0]
  have hR : (realVecE10CLM.comp realVecE01CLM) e0 0 = 0 := by
    simp [realVecE01CLM, realVecE10CLM, realMatrixToEuclideanCLM_apply, Fin.sum_univ_two, e0]
  rw [hL, hR] at h0
  exact one_ne_zero h0

/-- Instantiation of `IMapCLM_comp_rvdR` on `EuclideanSpace ℂ (Fin n)`. -/
theorem realVecSubmodule_IMapCLM_comp_rvdR (n : ℕ) :
    (IMapCLM (EuclideanSpace ℂ (Fin n))).comp
        (rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)) =
      (rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n)).comp
        (IMapCLM (EuclideanSpace ℂ (Fin n))) :=
  IMapCLM_comp_rvdR (realVecSubmodule n)

/-- Instantiation of `j_conj_rvdR` on `EuclideanSpace ℂ (Fin n)` with `vecConjLIE n`. -/
theorem realVecSubmodule_j_conj_rvdR (n : ℕ) :
    ((vecConjLIE n).toContinuousLinearEquiv :
          EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) *
        rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n) *
        ((vecConjLIE n).toContinuousLinearEquiv :
          EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) =
      (2 : ℝ) • (1 : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) -
        rvdR (H := EuclideanSpace ℂ (Fin n)) (realVecSubmodule n) := by
  refine j_conj_rvdR (realVecSubmodule n) (vecConjLIE n) ?_ ?_ ?_
  · intro x
    ext i
    simp [vecConjLIE]
  · intro x
    ext i
    simp [vecConjLIE, Complex.conj_I]
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      intro y hy
      have hre : ∀ i : Fin n, (w i).im = 0 := hw
      have hyre : ∀ i : Fin n, (y i).re = 0 := by
        rw [mem_imaginarySubmodule_iff] at hy
        intro i
        have hyi := hy i
        change ((-Complex.I : ℂ) * y i).im = 0 at hyi
        simpa [Complex.mul_im] using hyi
      change (⟪y, WithLp.toLp 2 (fun i => star (w i))⟫_ℂ).re = 0
      simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.star_def, Complex.re_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Complex.mul_re, hre i, hyre i]
    · intro hv
      rw [mem_symplCompSubmodule_iff] at hv
      have hveq : ∀ i : Fin n, (v i).im = 0 := by
        intro i
        let y : EuclideanSpace ℂ (Fin n) :=
          WithLp.toLp 2 (fun j => if j = i then (1 : ℂ) else 0)
        have hy : y ∈ realVecSubmodule n := by
          intro j
          by_cases hji : j = i
          · subst hji; simp [y]
          · simp [y, hji]
        have h0 := hv y hy
        simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.im_sum, y] at h0
        have hsum : (∑ j : Fin n, (v j *
            starRingEnd ℂ (if j = i then (1 : ℂ) else 0)).im) = (v i).im := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        rwa [hsum] at h0
      rw [Submodule.mem_map]
      refine ⟨v, hveq, ?_⟩
      ext i
      exact Complex.ext (by simp [vecConjLIE]) (by simp [vecConjLIE, hveq i])

end EuclideanSpaceInstantiation

/-! ### Instantiation 2: Hilbert–Schmidt `M_n(ℂ)` via `EuclideanSpace ℂ (Fin n × Fin n)` -/

section HilbertSchmidtMatrixInstantiation

/-- `ℂ`-linear isomorphism between `Matrix (Fin n) (Fin n) ℂ` and the Hilbert–Schmidt
space `EuclideanSpace ℂ (Fin n × Fin n)` without registering any global normed/inner
product instance on `Matrix (Fin n) (Fin n) ℂ`. -/
def toHS (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)
  invFun v := Matrix.of (fun i j => v (i, j))
  map_add' X Y := by ext ⟨i, j⟩; rfl
  map_smul' c X := by ext ⟨i, j⟩; rfl
  left_inv X := by ext i j; rfl
  right_inv v := by ext ⟨i, j⟩; rfl

theorem toHS_inner (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪toHS n X, toHS n Y⟫_ℂ = ComplexMatrixTomitaDuality.hsInner n X Y := by
  unfold ComplexMatrixTomitaDuality.hsInner
  simp only [PiLp.inner_apply, RCLike.inner_apply, toHS, LinearEquiv.coe_mk,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [RCLike.star_def, mul_comm]

/-- Tomita real standard subspace `K_F = {X ∈ M_n(ℂ) | (X * F.rInv)ᴴ = X * F.rInv}`
realized inside `EuclideanSpace ℂ (Fin n × Fin n)`. -/
def tomitaRealSubspace {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) where
  carrier := {v | ((toHS n).symm v * F.rInv)ᴴ = (toHS n).symm v * F.rInv}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    change (((toHS n).symm (x + y)) * F.rInv)ᴴ = (toHS n).symm (x + y) * F.rInv
    rw [map_add, Matrix.add_mul, Matrix.conjTranspose_add, hx, hy]
  smul_mem' := fun c {x} hx => by
    change (((toHS n).symm (c • x)) * F.rInv)ᴴ = (toHS n).symm (c • x) * F.rInv
    have hsmul : (toHS n).symm (c • x) = (c : ℂ) • (toHS n).symm x :=
      ((toHS n).symm.restrictScalars ℝ).map_smul c x
    rw [hsmul, Matrix.smul_mul, Matrix.conjTranspose_smul]
    change star (c : ℂ) • ((toHS n).symm x * F.rInv)ᴴ = (c : ℂ) • ((toHS n).symm x * F.rInv)
    rw [hx, Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem mem_tomitaRealSubspace_iff {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n)
    (v : EuclideanSpace ℂ (Fin n × Fin n)) :
    v ∈ tomitaRealSubspace F ↔ ((toHS n).symm v * F.rInv)ᴴ = (toHS n).symm v * F.rInv :=
  Iff.rfl

theorem isClosed_tomitaRealSubspace {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    IsClosed (tomitaRealSubspace F : Set (EuclideanSpace ℂ (Fin n × Fin n))) :=
  Submodule.closed_of_finiteDimensional (tomitaRealSubspace F)

instance {n : ℕ} (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    CompleteSpace (tomitaRealSubspace F) :=
  (isClosed_tomitaRealSubspace F).completeSpace_coe

instance {n : ℕ} (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    CompleteSpace
      (ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) :=
  completeSpace_imaginarySubmodule
    (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)

theorem tomitaRealSubspace_isStandard {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n) :
    IsStandardSubspace (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F) := by
  constructor
  · have htop :
        tomitaRealSubspace F ⊔
          ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      let X : Matrix (Fin n) (Fin n) ℂ := (toHS n).symm v
      let B : Matrix (Fin n) (Fin n) ℂ := X * F.rInv
      let Bh : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (B + Bᴴ)
      let Ba : Matrix (Fin n) (Fin n) ℂ := (-Complex.I / 2 : ℂ) • (B - Bᴴ)
      have hBh : Bhᴴ = Bh := by
        dsimp [Bh]
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
        have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
          simp
        rw [hhalf, add_comm]
      have hBa : Baᴴ = Ba := by
        dsimp [Ba]
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
        have hihalf : star (-Complex.I / 2 : ℂ) = (Complex.I / 2 : ℂ) := by
          simp
        rw [hihalf, ← neg_sub B Bᴴ, smul_neg, ← neg_smul]
        congr 1
        ring
      let vh : EuclideanSpace ℂ (Fin n × Fin n) := toHS n (Bh * F.r)
      let va : EuclideanSpace ℂ (Fin n × Fin n) := toHS n (Ba * F.r)
      have hvh : vh ∈ tomitaRealSubspace F := by
        rw [mem_tomitaRealSubspace_iff]
        have hsymm : (toHS n).symm vh = Bh * F.r := (toHS n).symm_apply_apply _
        rw [hsymm, Matrix.mul_assoc, F.r_mul_rInv, Matrix.mul_one]
        exact hBh
      have hva : (Complex.I : ℂ) • va ∈
          ImaginarySubmodule (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F) := by
        rw [mem_imaginarySubmodule_iff]
        have hinv : (-Complex.I : ℂ) • ((Complex.I : ℂ) • va) = va := by
          rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
        rw [hinv, mem_tomitaRealSubspace_iff]
        have hsymm : (toHS n).symm va = Ba * F.r := (toHS n).symm_apply_apply _
        rw [hsymm, Matrix.mul_assoc, F.r_mul_rInv, Matrix.mul_one]
        exact hBa
      have hsum : vh + (Complex.I : ℂ) • va = v := by
        apply (toHS n).symm.injective
        rw [map_add, (toHS n).symm.map_smul]
        have hsymm_h : (toHS n).symm vh = Bh * F.r := (toHS n).symm_apply_apply _
        have hsymm_a : (toHS n).symm va = Ba * F.r := (toHS n).symm_apply_apply _
        rw [hsymm_h, hsymm_a, ← Matrix.smul_mul, ← Matrix.add_mul]
        have hBdecomp : Bh + Complex.I • Ba = B := by
          dsimp [Bh, Ba]
          rw [smul_smul]
          have hI : Complex.I * (-Complex.I / 2 : ℂ) = (1 / 2 : ℂ) := by
            calc
              Complex.I * (-Complex.I / 2) = -(Complex.I * Complex.I) / 2 := by ring
              _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
          rw [hI, ← smul_add]
          have hadd : (B + Bᴴ) + (B - Bᴴ) = (2 : ℂ) • B := by
            ext i j
            simp
            ring
          rw [hadd, smul_smul]
          norm_num
        rw [hBdecomp]
        dsimp [B, X]
        rw [Matrix.mul_assoc, F.rInv_mul_r, Matrix.mul_one]
      rw [Submodule.mem_sup]
      exact ⟨vh, hvh, (Complex.I : ℂ) • va, hva, hsum⟩
    rw [htop]
    simp [dense_univ]
  · rw [eq_bot_iff]
    intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨h1, h2⟩
    rw [mem_imaginarySubmodule_iff] at h2
    rw [mem_tomitaRealSubspace_iff] at h1 h2
    have hsymm : (toHS n).symm ((-Complex.I : ℂ) • v) = (-Complex.I : ℂ) • (toHS n).symm v :=
      (toHS n).symm.map_smul _ _
    rw [hsymm, Matrix.smul_mul, Matrix.conjTranspose_smul] at h2
    have hstar : star (-Complex.I : ℂ) = Complex.I := by simp
    rw [hstar, h1] at h2
    have hzero : ((2 : ℂ) • ((toHS n).symm v * F.rInv)) = 0 := by
      have hneg : (Complex.I : ℂ) • ((toHS n).symm v * F.rInv) -
          (-Complex.I : ℂ) • ((toHS n).symm v * F.rInv) = 0 := sub_eq_zero.mpr h2
      have hI : ((2 * Complex.I : ℂ) • ((toHS n).symm v * F.rInv)) = 0 := by
        simpa [sub_eq_add_neg, neg_smul, add_smul, two_mul] using hneg
      have hB : (toHS n).symm v * F.rInv = 0 :=
        smul_eq_zero.mp hI |>.resolve_left (by simp [Complex.I_ne_zero])
      simp [hB]
    have hB0 : (toHS n).symm v * F.rInv = 0 :=
      smul_eq_zero.mp hzero |>.resolve_left (by norm_num)
    have hX0 : (toHS n).symm v = 0 := by
      calc
        (toHS n).symm v = ((toHS n).symm v * F.rInv) * F.r := by
          rw [Matrix.mul_assoc, F.rInv_mul_r, Matrix.mul_one]
        _ = 0 * F.r := by rw [hB0]
        _ = 0 := Matrix.zero_mul _
    exact (toHS n).symm.injective (by simpa using hX0)

/-- Conjugation operator `X ↦ U * X * Uᴴ` lifted to `EuclideanSpace ℂ (Fin n × Fin n)`. -/
def conjByCLM {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n × Fin n) :=
  let f : EuclideanSpace ℂ (Fin n × Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin n) :=
    { toFun := fun v => toHS n (U * (toHS n).symm v * Uᴴ)
      map_add' := fun x y => by
        rw [map_add, Matrix.mul_add, Matrix.add_mul, map_add]
      map_smul' := fun c x => by
        rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply] }
  f.toContinuousLinearMap

@[simp]
theorem conjByCLM_toHS {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ) :
    conjByCLM U (toHS n X) = toHS n (U * X * Uᴴ) := by
  change toHS n (U * (toHS n).symm (toHS n X) * Uᴴ) = toHS n (U * X * Uᴴ)
  rw [(toHS n).symm_apply_apply]

theorem conjByCLM_adjoint {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    (conjByCLM U).adjoint = conjByCLM Uᴴ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  let X := (toHS n).symm v
  let Y := (toHS n).symm w
  have hv : v = toHS n X := ((toHS n).apply_symm_apply v).symm
  have hw : w = toHS n Y := ((toHS n).apply_symm_apply w).symm
  rw [hv, hw, conjByCLM_toHS, conjByCLM_toHS, toHS_inner, toHS_inner]
  unfold ComplexMatrixTomitaDuality.hsInner
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc
    (Uᴴ * (Xᴴ * U) * Y).trace = (Uᴴ * (Xᴴ * U * Y)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Xᴴ * U * Y) * Uᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (Xᴴ * (U * Y * Uᴴ)).trace := by simp only [Matrix.mul_assoc]

theorem conjByCLM_preserves_tomitaRealSubspace {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * F.rInv = F.rInv * U) :
    ∀ v ∈ tomitaRealSubspace F, conjByCLM U v ∈ tomitaRealSubspace F := by
  intro v hv
  rw [mem_tomitaRealSubspace_iff] at hv ⊢
  let X := (toHS n).symm v
  have hX : (toHS n).symm (conjByCLM U v) = U * X * Uᴴ := by
    have hv' : v = toHS n X := ((toHS n).apply_symm_apply v).symm
    conv_lhs => rw [hv', conjByCLM_toHS]
    exact (toHS n).symm_apply_apply _
  rw [hX]
  have hU' : Uᴴ * F.rInv = F.rInv * Uᴴ := by
    have h := congrArg Matrix.conjTranspose hU
    simpa [Matrix.conjTranspose_mul, F.rInv_herm] using h.symm
  calc
    (U * X * Uᴴ * F.rInv)ᴴ = (U * (X * F.rInv) * Uᴴ)ᴴ := by
      rw [Matrix.mul_assoc (U * X) Uᴴ F.rInv, hU', ← Matrix.mul_assoc (U * X) F.rInv Uᴴ,
        Matrix.mul_assoc U X F.rInv]
    _ = (Uᴴ)ᴴ * (X * F.rInv)ᴴ * Uᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = U * (X * F.rInv) * Uᴴ := by
      rw [Matrix.conjTranspose_conjTranspose, hv]
    _ = U * X * (F.rInv * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = U * X * (Uᴴ * F.rInv) := by rw [← hU']
    _ = U * X * Uᴴ * F.rInv := by simp only [Matrix.mul_assoc]

/-- Any matrix `U` commuting with `F.rInv` induces a bounded conjugation operator
`conjByCLM U` commuting with `projK`, `projIK`, `rvdR`, and `rvdT` on `tomitaRealSubspace F`. -/
theorem conjByCLM_commutes_rvd {n : ℕ}
    (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * F.rInv = F.rInv * U) :
    ((conjByCLM U).restrictScalars ℝ).comp
          (projK (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (projK (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) ∧
      ((conjByCLM U).restrictScalars ℝ).comp
          (projIK (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (projIK (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) ∧
      ((conjByCLM U).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (rvdR (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) ∧
      ((conjByCLM U).restrictScalars ℝ).comp
          (rvdT (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (rvdT (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) := by
  have hU' : Uᴴ * F.rInv = F.rInv * Uᴴ := by
    have h := congrArg Matrix.conjTranspose hU
    simpa [Matrix.conjTranspose_mul, F.rInv_herm] using h.symm
  refine bounded_commutant_criterion_of_preserves_subspace (tomitaRealSubspace F)
    (conjByCLM U) (conjByCLM_preserves_tomitaRealSubspace F U hU) ?_
  rw [conjByCLM_adjoint]
  exact conjByCLM_preserves_tomitaRealSubspace F Uᴴ hU'

/-- Non-tracial diagonal `2 × 2` density factor `r = diag(2, 1)`, `rInv = diag(1/2, 1)`. -/
def diag2DensityFactor : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor 2 where
  r := Matrix.diagonal ![2, 1]
  rInv := Matrix.diagonal ![(1 / 2 : ℂ), 1]
  r_herm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  rInv_herm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  r_mul_rInv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rInv_mul_r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- For the non-tracial density factor `diag2DensityFactor`, `tomitaRealSubspace` is
genuinely non-orthogonal: `rvdR (tomitaRealSubspace diag2DensityFactor) ≠ 1`. -/
theorem diag2DensityFactor_rvdR_ne_one :
    rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2)) (tomitaRealSubspace diag2DensityFactor) ≠ 1 := by
  intro hEq
  let B1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![1, 0]]
  let B2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, Complex.I], ![-Complex.I, 0]]
  let v1 := toHS 2 (B1 * diag2DensityFactor.r)
  let v2 := (Complex.I : ℂ) • toHS 2 (B2 * diag2DensityFactor.r)
  have hv1 : v1 ∈ tomitaRealSubspace diag2DensityFactor := by
    rw [mem_tomitaRealSubspace_iff]
    have hsymm : (toHS 2).symm v1 = B1 * diag2DensityFactor.r := (toHS 2).symm_apply_apply _
    rw [hsymm, Matrix.mul_assoc, diag2DensityFactor.r_mul_rInv, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B1, Matrix.conjTranspose_apply]
  have hv2 : v2 ∈ ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) := by
    rw [mem_imaginarySubmodule_iff]
    have hinv : (-Complex.I : ℂ) • v2 = toHS 2 (B2 * diag2DensityFactor.r) := by
      dsimp [v2]
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rw [hinv, mem_tomitaRealSubspace_iff]
    have hsymm : (toHS 2).symm (toHS 2 (B2 * diag2DensityFactor.r)) =
        B2 * diag2DensityFactor.r := (toHS 2).symm_apply_apply _
    rw [hsymm, Matrix.mul_assoc, diag2DensityFactor.r_mul_rInv, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B2, Matrix.conjTranspose_apply]
  have hp1 : projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v1 = v1 :=
    (projK_eq_self_iff (tomitaRealSubspace diag2DensityFactor) v1).mpr hv1
  have hrvd1 : rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v1 = v1 := by
    rw [hEq]
    rfl
  have hprojIK0 : projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v1 = 0 := by
    have hadd : projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor) v1 +
        projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor) v1 = v1 := by
      simpa [rvdR] using hrvd1
    rw [hp1] at hadd
    exact add_left_cancel (hadd.trans (add_zero v1).symm)
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2 × Fin 2)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2))
  have horth : ⟪v1, v2⟫_ℝ = 0 := by
    have h := (ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor)).starProjection_inner_eq_zero v1 v2 hv2
    change ⟪v1 - projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v1, v2⟫_ℝ = 0 at h
    simpa [hprojIK0] using h
  have hM1 : B1 * diag2DensityFactor.r = Matrix.of ![![(0 : ℂ), 1], ![2, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B1, diag2DensityFactor, Matrix.mul_apply, Fin.sum_univ_two]
  have hM2 : B2 * diag2DensityFactor.r = Matrix.of ![![(0 : ℂ), Complex.I], ![-2 * Complex.I, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [B2, diag2DensityFactor, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  have hcalc : ⟪v1, v2⟫_ℝ = (3 : ℝ) := by
    change (⟪toHS 2 (B1 * diag2DensityFactor.r),
      toHS 2 (Complex.I • (B2 * diag2DensityFactor.r))⟫_ℂ).re = 3
    rw [toHS_inner, hM1, hM2]
    unfold ComplexMatrixTomitaDuality.hsInner
    simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    norm_num
  rw [hcalc] at horth
  norm_num at horth

/-- Concrete non-scalar diagonal unitary `U = diag(1, -1)` centralizing `diag2DensityFactor`. -/
def diag2CentralizerU : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), -1]

theorem diag2CentralizerU_commutes :
    diag2CentralizerU * diag2DensityFactor.rInv = diag2DensityFactor.rInv * diag2CentralizerU := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2CentralizerU, diag2DensityFactor, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- On the non-orthogonal standard subspace `tomitaRealSubspace diag2DensityFactor`,
conjugation by `diag2CentralizerU` commutes with `projK`, `projIK`, `rvdR`, and `rvdT`. -/
theorem diag2_centralizer_commutes_rvd :
    ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (rvdT (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (rvdT (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) :=
  conjByCLM_commutes_rvd diag2DensityFactor diag2CentralizerU diag2CentralizerU_commutes

end HilbertSchmidtMatrixInstantiation

end BoundedRealSubspaceBridge

end InfoGeometry.Modular.TomitaRegularCommutantAndKMSBridge
