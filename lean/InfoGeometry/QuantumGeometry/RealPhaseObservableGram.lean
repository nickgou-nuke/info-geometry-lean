/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Observable uncertainty with a real orthogonal phase

An actual real linear isometry `J` with square `-1` determines a skew form
`⟪J u,v⟫`. The block `[[C,-K],[K,C]]` is the native real Gram matrix of the
vectors `(v_a,J v_a)`. Its positivity and the two-vector uncertainty bound
follow from native Gram positivity and finite Bessel, respectively.

For actual symmetric real linear operators commuting with `J`, the phase
entry of the fluctuation Gram matrix equals minus one half of the phase-twisted
commutator expectation. No commutation between different observables is
assumed, and no complex scalar extension is used.

The fluctuation vectors use the unit-state expectation convention. For
`⟪ψ,ψ⟫ = 1` they are centered, and their Gram entries are the usual real
covariances. The Gram positivity and phase identities also hold for arbitrary
`ψ`, without asserting that the resulting quantities are statistical variances.

The two-vector Bessel proof generalizes the fixed doubled-carrier argument in
`Canonical.OperatorialUncertainty`. The present owner isolates its real
inner-product hypotheses and adds the actual observable commutator identity.
-/

noncomputable section

open scoped InnerProductSpace Matrix

namespace InfoGeometry.QuantumGeometry.RealPhaseObservableGram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (J : H ≃ₗᵢ[ℝ] H) (hJ : ∀ x, J (J x) = -x)

include hJ in
/-- An orthogonal square root of minus one is skew for the real inner product. -/
theorem inner_phase_left (u v : H) :
    ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ := by
  have h := J.inner_map_map (J u) v
  rw [hJ u, inner_neg_left] at h
  exact h.symm

include hJ in
@[simp] theorem inner_phase_self (u : H) : ⟪J u, u⟫_ℝ = 0 := by
  have hskew := inner_phase_left J hJ u u
  have hsym := real_inner_comm u (J u)
  linarith

include hJ in
@[simp] theorem inner_self_phase (u : H) : ⟪u, J u⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_phase_self J hJ u

/-- The phase part of a family of real vectors, with phase acting on the left. -/
def phaseGram {n : Type*} (v : n → H) : Matrix n n ℝ :=
  fun a b => ⟪J (v a), v b⟫_ℝ

include hJ in
theorem phaseGram_transpose {n : Type*} (v : n → H) :
    (phaseGram J v).transpose = -phaseGram J v := by
  ext a b
  change ⟪J (v b), v a⟫_ℝ = -⟪J (v a), v b⟫_ℝ
  rw [inner_phase_left J hJ, real_inner_comm (v b) (J (v a))]

include hJ in
/-- The real block is an actual Gram matrix, with the phase sign fixed by its family. -/
theorem real_block_eq_gram {n : Type*} (v : n → H) :
    Matrix.fromBlocks (Matrix.gram ℝ v) (-phaseGram J v)
      (phaseGram J v) (Matrix.gram ℝ v) =
        Matrix.gram ℝ (Sum.elim v (fun a => J (v a))) := by
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change -⟪J (v a), v b⟫_ℝ = ⟪v a, J (v b)⟫_ℝ
      linarith [inner_phase_left J hJ (v a) (v b)]
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change ⟪v a, v b⟫_ℝ = ⟪J (v a), J (v b)⟫_ℝ
      exact (J.inner_map_map (v a) (v b)).symm

include hJ in
theorem real_block_posSemidef {n : Type*} [Finite n] (v : n → H) :
    (Matrix.fromBlocks (Matrix.gram ℝ v) (-phaseGram J v)
      (phaseGram J v) (Matrix.gram ℝ v)).PosSemidef := by
  rw [real_block_eq_gram J hJ]
  exact Matrix.posSemidef_gram ℝ _

include hJ in
/-- Bessel's inequality on the perpendicular real pair `(u,J u)`. -/
theorem inner_sq_add_phase_inner_sq_le (u v : H) :
    ⟪u, v⟫_ℝ ^ 2 + ⟪J u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hJu : J u ≠ 0 := by
    intro h
    exact hu (J.injective (by simpa only [map_zero] using h))
  have hNormNe : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hOrth :
      ⟪NormedSpace.normalize u, NormedSpace.normalize (J u)⟫_ℝ = 0 := by
    rw [NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right, inner_self_phase J hJ]
    ring
  let w : Fin 2 → H := ![NormedSpace.normalize u, NormedSpace.normalize (J u)]
  have hw : Orthonormal ℝ w := by
    constructor
    · intro i
      fin_cases i
      · simpa [w] using NormedSpace.norm_normalize hu
      · simpa [w] using NormedSpace.norm_normalize hJu
    · intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction
      · simpa [w] using hOrth
      · simpa [w, real_inner_comm] using hOrth
      · contradiction
  have hBessel :
      ‖⟪NormedSpace.normalize u, v⟫_ℝ‖ ^ 2 +
        ‖⟪NormedSpace.normalize (J u), v⟫_ℝ‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa [w] using hw.sum_inner_products_le (x := v) (s := Finset.univ)
  have hScaled := mul_le_mul_of_nonneg_left hBessel (sq_nonneg ‖u‖)
  have hLhs :
      ‖u‖ ^ 2 * (‖⟪NormedSpace.normalize u, v⟫_ℝ‖ ^ 2 +
          ‖⟪NormedSpace.normalize (J u), v⟫_ℝ‖ ^ 2) =
        ⟪u, v⟫_ℝ ^ 2 + ⟪J u, v⟫_ℝ ^ 2 := by
    rw [NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_left,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, J.norm_map]
    field_simp [pow_two, hNormNe]
  rw [hLhs] at hScaled
  exact hScaled

/-- The fluctuation vector in the unit-state convention; it is centered when
`⟪ψ,ψ⟫ = 1`. -/
def fluctuation (ψ : H) (A : H →ₗ[ℝ] H) : H :=
  A ψ - ⟪ψ, A ψ⟫_ℝ • ψ

/-- The native Gram matrix of fluctuation vectors. For a unit state this is the
usual real covariance matrix. -/
def covariance {n : Type*} (ψ : H) (A : n → H →ₗ[ℝ] H) : Matrix n n ℝ :=
  Matrix.gram ℝ (fun a => fluctuation ψ (A a))

/-- The commutator convention corresponding to `⟪J v_a,v_b⟫`. -/
def commutatorMatrix {n : Type*} (ψ : H) (A : n → H →ₗ[ℝ] H) : Matrix n n ℝ :=
  fun a b => -(1 / 2 : ℝ) * ⟪ψ, J ((A a * A b - A b * A a) ψ)⟫_ℝ

theorem covariance_apply_eq_product {n : Type*} (ψ : H) (hψ : ⟪ψ, ψ⟫_ℝ = 1)
    (A : n → H →ₗ[ℝ] H) (a b : n) (hAa : (A a).IsSymmetric) :
    covariance ψ A a b =
      ⟪ψ, A a (A b ψ)⟫_ℝ - ⟪ψ, A a ψ⟫_ℝ * ⟪ψ, A b ψ⟫_ℝ := by
  simp only [covariance, Matrix.gram_apply, fluctuation,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hψ]
  rw [hAa ψ (A b ψ), real_inner_comm (A a ψ) ψ]
  simp only [mul_one, sub_self, sub_zero]

include hJ in
/-- A symmetric observable commuting with the phase has zero phase expectation. -/
theorem phase_apply_inner_self_zero (A : H →ₗ[ℝ] H) (hA : A.IsSymmetric)
    (hAJ : Function.Commute A J) (ψ : H) : ⟪J (A ψ), ψ⟫_ℝ = 0 := by
  have hskew := inner_phase_left J hJ (A ψ) ψ
  have hsym := hA ψ (J ψ)
  rw [hAJ ψ] at hsym
  have hcomm : ⟪A ψ, J ψ⟫_ℝ = ⟪ψ, J (A ψ)⟫_ℝ := hsym
  have hsymm : ⟪ψ, J (A ψ)⟫_ℝ = ⟪J (A ψ), ψ⟫_ℝ := real_inner_comm _ _
  rw [hsymm] at hcomm
  linarith

include hJ in
/-- The unit-state fluctuation correction leaves the phase cross term unchanged
for symmetric phase-commuting observables, for every `ψ`. -/
theorem phase_fluctuation_eq (ψ : H) (A B : H →ₗ[ℝ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAJ : Function.Commute A J) (hBJ : Function.Commute B J) :
    ⟪J (fluctuation ψ A), fluctuation ψ B⟫_ℝ = ⟪J (A ψ), B ψ⟫_ℝ := by
  have hA0 := phase_apply_inner_self_zero J hJ A hA hAJ ψ
  have hB0 : ⟪J ψ, B ψ⟫_ℝ = 0 := by
    have hBA := phase_apply_inner_self_zero J hJ B hB hBJ ψ
    have hBA' : ⟪ψ, J (B ψ)⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact hBA
    rw [inner_phase_left J hJ, hBA']
    simp
  simp only [fluctuation, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hA0, hB0,
    inner_phase_self J hJ ψ, mul_zero, sub_zero]

include hJ in
/-- The noncommutative operator identity fixes the sign and the factor one half. -/
theorem phase_inner_eq_commutator (ψ : H) (A B : H →ₗ[ℝ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAJ : Function.Commute A J) (hBJ : Function.Commute B J) :
    ⟪J (A ψ), B ψ⟫_ℝ =
      -(1 / 2 : ℝ) * ⟪ψ, J ((A * B - B * A) ψ)⟫_ℝ := by
  have hab : ⟪J (A ψ), B ψ⟫_ℝ = -⟪ψ, J (A (B ψ))⟫_ℝ := by
    rw [← hAJ ψ, hA (J ψ) (B ψ), inner_phase_left J hJ]
  have hba : ⟪J (A ψ), B ψ⟫_ℝ = ⟪ψ, J (B (A ψ))⟫_ℝ := by
    rw [← hB (J (A ψ)) ψ, hBJ (A ψ), real_inner_comm]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, inner_sub_right]
  linarith

include hJ in
theorem phase_fluctuation_eq_commutator (ψ : H) (A B : H →ₗ[ℝ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAJ : Function.Commute A J) (hBJ : Function.Commute B J) :
    ⟪J (fluctuation ψ A), fluctuation ψ B⟫_ℝ =
      -(1 / 2 : ℝ) * ⟪ψ, J ((A * B - B * A) ψ)⟫_ℝ := by
  rw [phase_fluctuation_eq J hJ ψ A B hA hB hAJ hBJ]
  exact phase_inner_eq_commutator J hJ ψ A B hA hB hAJ hBJ

include hJ in
theorem phaseGram_fluctuation_eq_commutatorMatrix {n : Type*}
    (ψ : H) (A : n → H →ₗ[ℝ] H)
    (hA : ∀ a, (A a).IsSymmetric) (hAJ : ∀ a, Function.Commute (A a) J) :
    phaseGram J (fun a => fluctuation ψ (A a)) = commutatorMatrix J ψ A := by
  ext a b
  exact phase_fluctuation_eq_commutator J hJ ψ (A a) (A b)
    (hA a) (hA b) (hAJ a) (hAJ b)

include hJ in
/-- Positive semidefiniteness of the complete real fluctuation-and-commutator
block. For a unit state its diagonal blocks are covariance matrices. -/
theorem real_uncertainty_block_posSemidef {n : Type*} [Finite n]
    (ψ : H) (A : n → H →ₗ[ℝ] H)
    (hA : ∀ a, (A a).IsSymmetric) (hAJ : ∀ a, Function.Commute (A a) J) :
    (Matrix.fromBlocks (covariance ψ A) (-commutatorMatrix J ψ A)
      (commutatorMatrix J ψ A) (covariance ψ A)).PosSemidef := by
  rw [← phaseGram_fluctuation_eq_commutatorMatrix J hJ ψ A hA hAJ]
  exact real_block_posSemidef J hJ (fun a => fluctuation ψ (A a))

include hJ in
/-- The two-observable Gram bound, interpreted as the covariance-inclusive
uncertainty relation when the state is normalized. -/
theorem two_observable_uncertainty {n : Type*}
    (ψ : H) (A : n → H →ₗ[ℝ] H) (a b : n)
    (hAa : (A a).IsSymmetric) (hAb : (A b).IsSymmetric)
    (hAJ : Function.Commute (A a) J) (hBJ : Function.Commute (A b) J) :
    covariance ψ A a b ^ 2 + commutatorMatrix J ψ A a b ^ 2 ≤
      covariance ψ A a a * covariance ψ A b b := by
  have h := inner_sq_add_phase_inner_sq_le J hJ
    (fluctuation ψ (A a)) (fluctuation ψ (A b))
  have hphase : ⟪J (fluctuation ψ (A a)), fluctuation ψ (A b)⟫_ℝ =
      commutatorMatrix J ψ A a b :=
    phase_fluctuation_eq_commutator J hJ ψ (A a) (A b) hAa hAb hAJ hBJ
  rw [hphase] at h
  simpa only [covariance, Matrix.gram_apply, real_inner_self_eq_norm_sq] using h

end InfoGeometry.QuantumGeometry.RealPhaseObservableGram
