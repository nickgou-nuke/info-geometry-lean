/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.FiniteDiracGramSquare
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.LinearCombination

/-!
# Finite observable covariance and the doubled Gram square

The observables are arbitrary full complex matrices.  For a state `ψ`, the
column with observable index `a` is the actual centered vector
`(A a - expectation ψ (A a) • 1) ψ`.  Its Gram matrix is positive semidefinite
without any commutativity assumption.  For a normalized state and Hermitian
observables its real and imaginary parts are, respectively, the symmetric
covariance and one half of the imaginary commutator expectation.

The rectangular column matrix is then passed to the existing finite Dirac
owner.  The observable Gram matrix is the right diagonal block of its square.
This is finite Hilbert-space algebra; it does not assert a spacetime Dirac
equation or positivity for an indefinite form.
-/

noncomputable section

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace InfoGeometry.QuantumGeometry.FiniteObservableGram

variable {d n : Type*} [Fintype d] [DecidableEq d]

/-- The actual vector-state expectation of a full complex matrix. -/
def expectation (ψ : EuclideanSpace ℂ d) (A : Matrix d d ℂ) : ℂ :=
  ⟪ψ, A.toEuclideanLin ψ⟫_ℂ

/-- Center the operator by its vector-state expectation. -/
def centeredOperator (ψ : EuclideanSpace ℂ d) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  A - expectation ψ A • 1

/-- The fluctuation vector of a matrix in the chosen state. -/
def fluctuation (ψ : EuclideanSpace ℂ d) (A : Matrix d d ℂ) : EuclideanSpace ℂ d :=
  A.toEuclideanLin ψ - expectation ψ A • ψ

/-- One actual fluctuation vector in each observable-indexed column. -/
def fluctuationColumns (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) : Matrix d n ℂ :=
  fun i a => fluctuation ψ (A a) i

/-- The native Gram matrix of the observable fluctuation vectors. -/
def uncertaintyGram (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) : Matrix n n ℂ :=
  Matrix.gram ℂ (fun a => fluctuation ψ (A a))

/-- The real covariance matrix; its observable formula is proved below. -/
def covariance (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) : Matrix n n ℝ :=
  (uncertaintyGram ψ A).map Complex.re

/-- Half the imaginary commutator expectation. For Hermitian observables this
is the real value of the convention `1/(2i) ⟨[A,B]⟩`. -/
def commutatorMatrix (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) : Matrix n n ℝ :=
  fun a b => (expectation ψ (A a * A b - A b * A a)).im / 2

@[simp] theorem expectation_add (ψ : EuclideanSpace ℂ d) (A B : Matrix d d ℂ) :
    expectation ψ (A + B) = expectation ψ A + expectation ψ B := by
  simp [expectation, inner_add_right]

@[simp] theorem expectation_sub (ψ : EuclideanSpace ℂ d) (A B : Matrix d d ℂ) :
    expectation ψ (A - B) = expectation ψ A - expectation ψ B := by
  simp [expectation, inner_sub_right]

@[simp] theorem expectation_smul (ψ : EuclideanSpace ℂ d) (c : ℂ) (A : Matrix d d ℂ) :
    expectation ψ (c • A) = c * expectation ψ A := by
  simp [expectation, inner_smul_right]

/-- Hermitian observables have real expectation in every state, normalized or not. -/
theorem expectation_conj (ψ : EuclideanSpace ℂ d) {A : Matrix d d ℂ}
    (hA : A.IsHermitian) :
    starRingEnd ℂ (expectation ψ A) = expectation ψ A := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  calc
    starRingEnd ℂ (expectation ψ A) = ⟪A.toEuclideanLin ψ, ψ⟫_ℂ :=
      inner_conj_symm _ _
    _ = expectation ψ A := hsym ψ ψ

theorem expectation_im (ψ : EuclideanSpace ℂ d) {A : Matrix d d ℂ}
    (hA : A.IsHermitian) : (expectation ψ A).im = 0 := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply ψ

/-- Multiplication order is retained when moving a Hermitian observable across the pairing. -/
theorem expectation_mul (ψ : EuclideanSpace ℂ d) {A : Matrix d d ℂ}
    (hA : A.IsHermitian) (B : Matrix d d ℂ) :
    expectation ψ (A * B) = ⟪A.toEuclideanLin ψ, B.toEuclideanLin ψ⟫_ℂ := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  calc
    expectation ψ (A * B) = ⟪ψ, A.toEuclideanLin (B.toEuclideanLin ψ)⟫_ℂ := by
      simp [expectation, Matrix.toEuclideanLin]
    _ = ⟪A.toEuclideanLin ψ, B.toEuclideanLin ψ⟫_ℂ := (hsym _ _).symm

/-- The column definition really is the action of the centered matrix. -/
theorem fluctuation_eq_centered_apply (ψ : EuclideanSpace ℂ d) (A : Matrix d d ℂ) :
    fluctuation ψ A = (centeredOperator ψ A).toEuclideanLin ψ := by
  simp [fluctuation, centeredOperator, Matrix.toEuclideanLin]

/-- Normalization makes the fluctuation orthogonal to the state. -/
theorem inner_state_fluctuation (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : Matrix d d ℂ) :
    ⟪ψ, fluctuation ψ A⟫_ℂ = 0 := by
  simp only [fluctuation, inner_sub_right, inner_smul_right, hψ, mul_one]
  exact sub_self _

/-- Expansion of centered inner products before imposing Hermitian hypotheses. -/
theorem fluctuation_inner (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A B : Matrix d d ℂ) :
    ⟪fluctuation ψ A, fluctuation ψ B⟫_ℂ =
      ⟪A.toEuclideanLin ψ, B.toEuclideanLin ψ⟫_ℂ -
        starRingEnd ℂ (expectation ψ A) * expectation ψ B := by
  have hconj : starRingEnd ℂ (expectation ψ A) = ⟪A.toEuclideanLin ψ, ψ⟫_ℂ :=
    inner_conj_symm _ _
  simp only [fluctuation, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hψ, mul_one]
  rw [← hconj]
  simp only [sub_self, mul_zero, sub_zero, expectation]

@[simp] theorem uncertaintyGram_apply (ψ : EuclideanSpace ℂ d)
    (A : n → Matrix d d ℂ) (a b : n) :
    uncertaintyGram ψ A a b = ⟪fluctuation ψ (A a), fluctuation ψ (A b)⟫_ℂ := rfl

/-- The Gram entry is the ordered product expectation minus the product of means. -/
theorem uncertaintyGram_apply_eq_product (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ) (a b : n)
    (hAa : (A a).IsHermitian) :
    uncertaintyGram ψ A a b =
      expectation ψ (A a * A b) - expectation ψ (A a) * expectation ψ (A b) := by
  rw [uncertaintyGram_apply, fluctuation_inner ψ hψ,
    ← expectation_mul ψ hAa, expectation_conj ψ hAa]

theorem uncertaintyGram_isHermitian (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    (uncertaintyGram ψ A).IsHermitian :=
  Matrix.isHermitian_gram ℂ _

theorem uncertaintyGram_posSemidef [Fintype n] (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    (uncertaintyGram ψ A).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

/-- The full complex coefficient quadratic form is a squared norm, not a pairwise proxy. -/
theorem uncertaintyGram_quadratic [Fintype n] (ψ : EuclideanSpace ℂ d)
    (A : n → Matrix d d ℂ) (z : n → ℂ) :
    star z ⬝ᵥ (uncertaintyGram ψ A *ᵥ z) =
      (‖∑ a, z a • fluctuation ψ (A a)‖ : ℂ) ^ 2 := by
  rw [uncertaintyGram, Matrix.star_dotProduct_gram_mulVec]
  exact inner_self_eq_norm_sq_to_K _

theorem covariance_transpose (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    (covariance ψ A)ᵀ = covariance ψ A := by
  ext a b
  change (⟪fluctuation ψ (A b), fluctuation ψ (A a)⟫_ℂ).re =
    (⟪fluctuation ψ (A a), fluctuation ψ (A b)⟫_ℂ).re
  exact inner_re_symm (𝕜 := ℂ) _ _

/-- Restricting the Hilbert pairing to real scalars proves real covariance positivity. -/
theorem covariance_posSemidef [Fintype n] (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    (covariance ψ A).PosSemidef := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ d) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ d)
  change (Matrix.gram ℝ (fun a => fluctuation ψ (A a))).PosSemidef
  exact Matrix.posSemidef_gram ℝ _

/-- Actual symmetric observable covariance, with no commutativity of `A a` and `A b`. -/
theorem covariance_eq_symmetrized_expectation (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ) (a b : n)
    (hAa : (A a).IsHermitian) (hAb : (A b).IsHermitian) :
    covariance ψ A a b =
      (expectation ψ (A a * A b + A b * A a)).re / 2 -
        (expectation ψ (A a)).re * (expectation ψ (A b)).re := by
  have hab := congrArg Complex.re (uncertaintyGram_apply_eq_product ψ hψ A a b hAa)
  have hba := congrArg Complex.re (uncertaintyGram_apply_eq_product ψ hψ A b a hAb)
  have hsym := congrArg (fun M : Matrix n n ℝ => M a b) (covariance_transpose ψ A)
  simp only [Complex.sub_re, Complex.mul_re, expectation_im ψ hAa,
    expectation_im ψ hAb, zero_mul, sub_zero] at hab hba
  change (uncertaintyGram ψ A b a).re = (uncertaintyGram ψ A a b).re at hsym
  simp only [covariance, Matrix.map_apply, expectation_add, Complex.add_re]
  -- The remaining identity is between real parts of the scalar pairings.
  linear_combination (hab + hba - hsym) / 2

/-- The antisymmetric defect is exactly the ordered commutator expectation. -/
theorem uncertaintyGram_sub_swap (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ) (a b : n)
    (hAa : (A a).IsHermitian) (hAb : (A b).IsHermitian) :
    uncertaintyGram ψ A a b - uncertaintyGram ψ A b a =
      expectation ψ (A a * A b - A b * A a) := by
  rw [uncertaintyGram_apply_eq_product ψ hψ A a b hAa,
    uncertaintyGram_apply_eq_product ψ hψ A b a hAb, expectation_sub]
  rw [mul_comm (expectation ψ (A b)) (expectation ψ (A a))]
  abel

/-- This fixes the factor and sign connecting the imaginary Gram part to the commutator. -/
theorem uncertaintyGram_im (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ) (a b : n)
    (hAa : (A a).IsHermitian) (hAb : (A b).IsHermitian) :
    (uncertaintyGram ψ A a b).im = commutatorMatrix ψ A a b := by
  have hswap : -(uncertaintyGram ψ A b a).im = (uncertaintyGram ψ A a b).im :=
    (inner_im_symm (𝕜 := ℂ) (fluctuation ψ (A a)) (fluctuation ψ (A b))).symm
  have hcomm := congrArg Complex.im (uncertaintyGram_sub_swap ψ hψ A a b hAa hAb)
  simp only [Complex.sub_im] at hcomm
  unfold commutatorMatrix
  linear_combination (hcomm - hswap) / 2

theorem commutatorMatrix_transpose (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    (commutatorMatrix ψ A)ᵀ = -commutatorMatrix ψ A := by
  ext a b
  simp only [commutatorMatrix, Matrix.transpose_apply, Matrix.neg_apply,
    expectation_sub, Complex.sub_im]
  ring

/-- The complete covariance-plus-commutator matrix is the observable Gram matrix. -/
theorem uncertaintyGram_decomposition (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    uncertaintyGram ψ A =
      (covariance ψ A).map Complex.ofReal +
        Complex.I • (commutatorMatrix ψ A).map Complex.ofReal := by
  ext a b
  change uncertaintyGram ψ A a b =
    ((uncertaintyGram ψ A a b).re : ℂ) + Complex.I * (commutatorMatrix ψ A a b : ℂ)
  rw [← uncertaintyGram_im ψ hψ A a b (hA a) (hA b)]
  simpa only [mul_comm] using (Complex.re_add_im (uncertaintyGram ψ A a b)).symm

/-- The `n`-observable matrix uncertainty inequality. -/
theorem covariance_add_I_commutator_posSemidef [Fintype n] (ψ : EuclideanSpace ℂ d)
    (hψ : ⟪ψ, ψ⟫_ℂ = 1) (A : n → Matrix d d ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    ((covariance ψ A).map Complex.ofReal +
      Complex.I • (commutatorMatrix ψ A).map Complex.ofReal).PosSemidef := by
  rw [← uncertaintyGram_decomposition ψ hψ A hA]
  exact uncertaintyGram_posSemidef ψ A

/-- Identification with the existing rectangular-matrix Gram owner. -/
theorem uncertaintyGram_eq_rightGram (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    uncertaintyGram ψ A =
      InfoGeometry.Krein.FiniteDiracGramSquare.rightGram (fluctuationColumns ψ A) := by
  have hcol (a : n) : WithLp.toLp 2 ((fluctuationColumns ψ A)ᵀ a) =
      fluctuation ψ (A a) := by
    ext i
    rfl
  ext a b
  simpa only [hcol, uncertaintyGram_apply,
    InfoGeometry.Krein.FiniteDiracGramSquare.rightGram] using
      (inner_matrix_col_col (fluctuationColumns ψ A) (fluctuationColumns ψ A) a b)

variable [Fintype n] [DecidableEq n]

/-- The doubled operator square has the actual observable uncertainty matrix as its right block. -/
theorem fluctuation_dirac_sq (ψ : EuclideanSpace ℂ d) (A : n → Matrix d d ℂ) :
    let T := fluctuationColumns ψ A
    InfoGeometry.Krein.FiniteDiracGramSquare.dirac T *
        InfoGeometry.Krein.FiniteDiracGramSquare.dirac T =
      Matrix.fromBlocks (InfoGeometry.Krein.FiniteDiracGramSquare.leftGram T)
        0 0 (uncertaintyGram ψ A) := by
  dsimp only
  rw [InfoGeometry.Krein.FiniteDiracGramSquare.dirac_sq, uncertaintyGram_eq_rightGram]

/-- Entry-level readout of the same right block, suitable for downstream consumers. -/
theorem fluctuation_dirac_sq_right_block (ψ : EuclideanSpace ℂ d)
    (A : n → Matrix d d ℂ) (a b : n) :
    (InfoGeometry.Krein.FiniteDiracGramSquare.dirac (fluctuationColumns ψ A) *
      InfoGeometry.Krein.FiniteDiracGramSquare.dirac (fluctuationColumns ψ A))
        (Sum.inr a) (Sum.inr b) = uncertaintyGram ψ A a b := by
  rw [fluctuation_dirac_sq]
  rfl

end InfoGeometry.QuantumGeometry.FiniteObservableGram

end
