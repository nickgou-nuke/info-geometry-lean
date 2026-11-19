/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.QuantumGeometry.FiniteObservableGram
import Mathlib.Basic.Complex.BigOperators

/-!
# Observable-index congruence and real uncertainty form

Column coefficients mix the observables before expectation or centering.
Complex coefficient changes act on their Gram matrix by Hermitian congruence.
Real coefficient changes preserve Hermitian observables and act on both the
covariance and commutator matrices by ordinary transpose congruence.

The real block matrix `[[C,-K],[K,C]]` is the real Gram matrix of the vectors
`v a` and `I • v a`.  Its positivity is derived from that actual real Hilbert
pairing, not inferred for an indefinite doubling.
-/

noncomputable section

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace InfoGeometry.QuantumGeometry.FiniteObservableGram

variable {d n k : Type*} [Fintype d] [DecidableEq d]
variable [Fintype n]

/-- Column coefficients mix full matrices before taking any expectation. -/
def mixObservables (C : Matrix n k ℂ) (A : n → Matrix d d ℂ) : k → Matrix d d ℂ :=
  fun b => ∑ a, C a b • A a

/-- Centering is complex linear in the operator argument. -/
theorem fluctuation_mixObservables (ψ : EuclideanSpace ℂ d)
    (C : Matrix n k ℂ) (A : n → Matrix d d ℂ) (b : k) :
    fluctuation ψ (mixObservables C A b) =
      ∑ a, C a b • fluctuation ψ (A a) := by
  simp [fluctuation, expectation, mixObservables, _root_.sum_apply,
    inner_sum, inner_smul_right, Finset.sum_smul,
    Finset.sum_sub_distrib, smul_sub, mul_smul]

/-- Rectangular changes of observable coefficients act by Hermitian congruence. -/
theorem uncertaintyGram_mixObservables (ψ : EuclideanSpace ℂ d)
    (C : Matrix n k ℂ) (A : n → Matrix d d ℂ) :
    uncertaintyGram ψ (mixObservables C A) = Cᴴ * uncertaintyGram ψ A * C := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [uncertaintyGram_apply, fluctuation_mixObservables,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [Fintype d] [DecidableEq d] in
/-- Real coefficient changes preserve the Hermitian observable class. -/
theorem mixObservables_real_isHermitian (C : Matrix n k ℝ)
    (A : n → Matrix d d ℂ) (hA : ∀ a, (A a).IsHermitian) (b : k) :
    (mixObservables (C.map Complex.ofReal) A b).IsHermitian := by
  change (∑ a, (C a b : ℂ) • A a)ᴴ = ∑ a, (C a b : ℂ) • A a
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, (hA a).eq]
  simp

/-- The real covariance transforms by ordinary congruence for real column coefficients. -/
theorem covariance_mixObservables_real (ψ : EuclideanSpace ℂ d)
    (C : Matrix n k ℝ) (A : n → Matrix d d ℂ) :
    covariance ψ (mixObservables (C.map Complex.ofReal) A) =
      Cᵀ * covariance ψ A * C := by
  ext a b
  have h := congrArg (fun M : Matrix k k ℂ => (M a b).re)
    (uncertaintyGram_mixObservables ψ (C.map Complex.ofReal) A)
  simpa only [covariance, Matrix.map_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using h

omit [Fintype n] in
/-- Matrix-level conversion from commutator expectations to the imaginary Gram part. -/
theorem commutatorMatrix_eq_im (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    commutatorMatrix ψ A = (uncertaintyGram ψ A).map Complex.im := by
  ext a b
  exact (uncertaintyGram_im ψ hψ A a b (hA a) (hA b)).symm

/-- The commutator matrix transforms by the same real congruence, with its sign intact. -/
theorem commutatorMatrix_mixObservables_real (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (C : Matrix n k ℝ)
    (A : n → Matrix d d ℂ) (hA : ∀ a, (A a).IsHermitian) :
    commutatorMatrix ψ (mixObservables (C.map Complex.ofReal) A) =
      Cᵀ * commutatorMatrix ψ A * C := by
  rw [commutatorMatrix_eq_im ψ hψ _ (mixObservables_real_isHermitian C A hA),
    commutatorMatrix_eq_im ψ hψ A hA]
  ext a b
  have h := congrArg (fun M : Matrix k k ℂ => (M a b).im)
    (uncertaintyGram_mixObservables ψ (C.map Complex.ofReal) A)
  simpa only [Matrix.map_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_ofReal, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero] using h

/-- A genuine real Gram realization of the full complex uncertainty form.
The first half of the family is `v a`; the second half is `I • v a`. -/
theorem real_uncertainty_block_posSemidef (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    (Matrix.fromBlocks (covariance ψ A) (-commutatorMatrix ψ A)
      (commutatorMatrix ψ A) (covariance ψ A)).PosSemidef := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ d) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ d)
  let v : n ⊕ n → EuclideanSpace ℂ d :=
    Sum.elim (fun a => fluctuation ψ (A a))
      (fun a => Complex.I • fluctuation ψ (A a))
  have hblock : Matrix.gram ℝ v =
      Matrix.fromBlocks (covariance ψ A) (-commutatorMatrix ψ A)
        (commutatorMatrix ψ A) (covariance ψ A) := by
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b =>
        change (⟪fluctuation ψ (A a), Complex.I • fluctuation ψ (A b)⟫_ℂ).re =
          -commutatorMatrix ψ A a b
        rw [inner_smul_right]
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
          zero_mul, one_mul, zero_sub]
        exact congrArg Neg.neg (uncertaintyGram_im ψ hψ A a b (hA a) (hA b))
    | inr a =>
      cases b with
      | inl b =>
        change (⟪Complex.I • fluctuation ψ (A a), fluctuation ψ (A b)⟫_ℂ).re =
          commutatorMatrix ψ A a b
        simp only [inner_smul_left, Complex.conj_I, Complex.mul_re,
          Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im]
        simpa using uncertaintyGram_im ψ hψ A a b (hA a) (hA b)
      | inr b =>
        change (⟪Complex.I • fluctuation ψ (A a),
          Complex.I • fluctuation ψ (A b)⟫_ℂ).re =
            (⟪fluctuation ψ (A a), fluctuation ψ (A b)⟫_ℂ).re
        rw [inner_smul_left, inner_smul_right, ← mul_assoc]
        simp
  rw [← hblock]
  exact Matrix.posSemidef_gram ℝ v

omit [Fintype n] in
/-- Every two-observable minor obeys the covariance-inclusive uncertainty bound. -/
theorem two_observable_uncertainty (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ) (a b : n)
    (hAa : (A a).IsHermitian) (hAb : (A b).IsHermitian) :
    (covariance ψ A a b) ^ 2 + (commutatorMatrix ψ A a b) ^ 2 ≤
      covariance ψ A a a * covariance ψ A b b := by
  have hnorm := norm_inner_le_norm (𝕜 := ℂ)
    (fluctuation ψ (A a)) (fluctuation ψ (A b))
  have hsq : Complex.normSq (uncertaintyGram ψ A a b) ≤
      ‖fluctuation ψ (A a)‖ ^ 2 * ‖fluctuation ψ (A b)‖ ^ 2 := by
    rw [uncertaintyGram_apply, Complex.normSq_eq_norm_sq]
    calc
      ‖⟪fluctuation ψ (A a), fluctuation ψ (A b)⟫_ℂ‖ ^ 2 ≤
          (‖fluctuation ψ (A a)‖ * ‖fluctuation ψ (A b)‖) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  have hdiag (i : n) : covariance ψ A i i = ‖fluctuation ψ (A i)‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (fluctuation ψ (A i))).symm
  rw [← hdiag a, ← hdiag b, Complex.normSq_apply,
    uncertaintyGram_im ψ hψ A a b hAa hAb] at hsq
  simpa only [covariance, Matrix.map_apply, pow_two] using hsq

end InfoGeometry.QuantumGeometry.FiniteObservableGram

end
