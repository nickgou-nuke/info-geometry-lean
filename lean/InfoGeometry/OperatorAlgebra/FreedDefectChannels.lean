/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Algebra.SupermatrixKoszul
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Complementary cuts, scaled defects, and positive Gram channels

The matrix results retain arbitrary noncommutative coefficients. Nonunit
statements require a nontrivial coefficient ring. The Walsh elements are
scaled idempotents, not projections without an additional normalization.

Cut composition and Gram factorization are proved in any ring and star ring,
respectively. Actual nonnegativity uses Mathlib's `StarOrderedRing`. No
cobordism functor or categorical defect theory is constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.FreedDefectChannels

open Matrix InfoGeometry.Algebra.SupermatrixKoszul

section Cuts

variable {B : Type*} [Ring B]

/-- Resolving a composition across a complementary cut uses no star or
idempotence assumption. -/
theorem cut_composition (p X Y : B) :
    X * p * Y + X * (1 - p) * Y = X * Y := by
  noncomm_ring

variable [StarRing B]

/-- A channel through a self-adjoint idempotent is explicitly a Gram square. -/
theorem cut_channel_gram (p Z : B) (hp : p * p = p) (hstar : star p = p) :
    Z * p * star Z = (Z * p) * star (Z * p) := by
  rw [star_mul, hstar]
  simp only [mul_assoc, ← mul_assoc p p, hp]

theorem cut_channel_selfAdjoint (p Z : B) (hstar : star p = p) :
    IsSelfAdjoint (Z * p * star Z) := by
  show star (Z * p * star Z) = Z * p * star Z
  simp [star_mul, hstar, mul_assoc]

/-- Both complementary channels are Gram squares, without an order on `B`. -/
theorem cut_double_gram (p Z : B) (hp : p * p = p) (hstar : star p = p) :
    Z * star Z = (Z * p) * star (Z * p) +
      (Z * (1 - p)) * star (Z * (1 - p)) := by
  have hq : (1 - p) * (1 - p) = 1 - p := by
    calc
      (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
      _ = 1 - p := by rw [hp]; abel
  have hqstar : star (1 - p) = 1 - p := by simp [hstar]
  rw [← cut_channel_gram p Z hp hstar, ← cut_channel_gram (1 - p) Z hq hqstar]
  exact (cut_composition p Z (star Z)).symm

/-- Positivity is a consequence of an explicit star order and the Gram
factorization, rather than a synonym for self-adjointness. -/
theorem cut_channel_nonneg [PartialOrder B] [StarOrderedRing B]
    (p Z : B) (hp : p * p = p) (hstar : star p = p) :
    0 ≤ Z * p * star Z := by
  rw [cut_channel_gram p Z hp hstar]
  exact mul_star_self_nonneg (Z * p)

end Cuts

section MatrixDefects

variable {R : Type*} [Ring R]

theorem plus_cut_idempotent :
    evenBlock (1 : R) 0 * evenBlock 1 0 = evenBlock 1 0 := by
  rw [evenBlock_mul_evenBlock]
  simp

theorem minus_cut_idempotent :
    evenBlock (0 : R) 1 * evenBlock 0 1 = evenBlock 0 1 := by
  rw [evenBlock_mul_evenBlock]
  simp

theorem plus_minus_cuts_zero : evenBlock (1 : R) 0 * evenBlock 0 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenBlock, Matrix.mul_apply, Fin.sum_univ_two]

theorem plus_cut_complement :
    1 - evenBlock (1 : R) 0 = evenBlock 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenBlock]

/-- The whole centralizer of the first Peirce projector. -/
theorem commute_plus_cut_iff (H : Matrix (Fin 2) (Fin 2) R) :
    Commute (evenBlock 1 0) H ↔ H 0 1 = 0 ∧ H 1 0 = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h.eq
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) h.eq
    constructor
    · simpa [evenBlock, Matrix.mul_apply, Fin.sum_univ_two] using h01
    · simpa [evenBlock, Matrix.mul_apply, Fin.sum_univ_two] using h10.symm
  · rintro ⟨h01, h10⟩
    show evenBlock 1 0 * H = H * evenBlock 1 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenBlock, Matrix.mul_apply, Fin.sum_univ_two, h01, h10]

/-- The whole centralizer of the swap, over arbitrary ring coefficients. -/
theorem commute_swap_iff (H : Matrix (Fin 2) (Fin 2) R) :
    Commute (oddBlock 1 1) H ↔ H 0 0 = H 1 1 ∧ H 0 1 = H 1 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h.eq
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h.eq
    constructor
    · simpa [oddBlock, Matrix.mul_apply, Fin.sum_univ_two] using h01.symm
    · simpa [oddBlock, Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
  · rintro ⟨hdiag, hoff⟩
    show oddBlock 1 1 * H = H * oddBlock 1 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oddBlock, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hoff]

def walshPlus : Matrix (Fin 2) (Fin 2) R := 1 + oddBlock 1 1
def walshMinus : Matrix (Fin 2) (Fin 2) R := 1 - oddBlock 1 1

theorem swap_sq : oddBlock (1 : R) 1 * oddBlock 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddBlock, Matrix.mul_apply, Fin.sum_univ_two]

theorem walshPlus_mul_walshMinus : (walshPlus : Matrix (Fin 2) (Fin 2) R) * walshMinus = 0 := by
  unfold walshPlus walshMinus
  noncomm_ring [swap_sq (R := R)]

theorem walshMinus_mul_walshPlus : (walshMinus : Matrix (Fin 2) (Fin 2) R) * walshPlus = 0 := by
  unfold walshPlus walshMinus
  noncomm_ring [swap_sq (R := R)]

theorem walshPlus_scaled_idempotent :
    (walshPlus : Matrix (Fin 2) (Fin 2) R) * walshPlus = walshPlus + walshPlus := by
  unfold walshPlus
  noncomm_ring [swap_sq (R := R)]

theorem walshMinus_scaled_idempotent :
    (walshMinus : Matrix (Fin 2) (Fin 2) R) * walshMinus = walshMinus + walshMinus := by
  unfold walshMinus
  noncomm_ring [swap_sq (R := R)]

/-- Adding the identity preserves the swap centralizer exactly. -/
theorem commute_walshPlus_iff (H : Matrix (Fin 2) (Fin 2) R) :
    Commute walshPlus H ↔ H 0 0 = H 1 1 ∧ H 0 1 = H 1 0 := by
  rw [← commute_swap_iff]
  simp [Commute, SemiconjBy, walshPlus, add_mul, mul_add]

theorem commute_walshMinus_iff (H : Matrix (Fin 2) (Fin 2) R) :
    Commute walshMinus H ↔ H 0 0 = H 1 1 ∧ H 0 1 = H 1 0 := by
  rw [← commute_swap_iff]
  simp [Commute, SemiconjBy, walshMinus, sub_mul, mul_sub]

theorem plus_cut_commute_diagonal (a d : R) :
    Commute (evenBlock 1 0) (evenBlock a d) := by
  simp [commute_plus_cut_iff]

theorem minus_cut_commute_diagonal (a d : R) :
    Commute (evenBlock 0 1) (evenBlock a d) := by
  show evenBlock 0 1 * evenBlock a d = evenBlock a d * evenBlock 0 1
  simp only [evenBlock_mul_evenBlock, zero_mul, one_mul, mul_zero, mul_one]

theorem walshPlus_commute_symmetric (h0 h1 : R) :
    Commute walshPlus (evenBlock h0 h0 + oddBlock h1 h1) := by
  simp [commute_walshPlus_iff]

theorem walshMinus_commute_symmetric (h0 h1 : R) :
    Commute walshMinus (evenBlock h0 h0 + oddBlock h1 h1) := by
  simp [commute_walshMinus_iff]

theorem plus_cut_not_isUnit [Nontrivial R] :
    ¬ IsUnit (evenBlock (1 : R) 0) := by
  intro h
  have hz := h.mul_right_eq_zero.mp (plus_minus_cuts_zero (R := R))
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hz
  simp at h11

theorem minus_cut_not_isUnit [Nontrivial R] :
    ¬ IsUnit (evenBlock (0 : R) 1) := by
  intro h
  have hz := h.mul_left_eq_zero.mp (plus_minus_cuts_zero (R := R))
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hz
  simp at h00

theorem walshPlus_not_isUnit [Nontrivial R] :
    ¬ IsUnit (walshPlus : Matrix (Fin 2) (Fin 2) R) := by
  intro h
  have hz := h.mul_right_eq_zero.mp (walshPlus_mul_walshMinus (R := R))
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hz
  simp [walshMinus, oddBlock] at h00

theorem walshMinus_not_isUnit [Nontrivial R] :
    ¬ IsUnit (walshMinus : Matrix (Fin 2) (Fin 2) R) := by
  intro h
  have hz := h.mul_right_eq_zero.mp (walshMinus_mul_walshPlus (R := R))
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hz
  simp [walshPlus, oddBlock] at h00

/-- In characteristic two the two scaled defects coincide. -/
theorem walsh_eq_of_two_eq_zero (h2 : (2 : R) = 0) :
    (walshPlus : Matrix (Fin 2) (Fin 2) R) = walshMinus := by
  have hneg : -(1 : R) = 1 := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa [one_add_one_eq_two] using h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [walshPlus, walshMinus, oddBlock, hneg]

/-- In characteristic two the symmetric defect is square-zero. -/
theorem walsh_sq_zero_of_two_eq_zero (h2 : (2 : R) = 0) :
    (walshPlus : Matrix (Fin 2) (Fin 2) R) * walshPlus = 0 := by
  calc
    _ = walshPlus * walshMinus :=
      congrArg (fun Q => (walshPlus : Matrix (Fin 2) (Fin 2) R) * Q)
        (walsh_eq_of_two_eq_zero h2)
    _ = 0 := walshPlus_mul_walshMinus

end MatrixDefects

section MatrixChannels

variable {R : Type*} [Ring R] [StarRing R]

theorem plus_cut_star : star (evenBlock (1 : R) 0) = evenBlock 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenBlock]

theorem minus_cut_star : star (evenBlock (0 : R) 1) = evenBlock 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenBlock]

theorem plus_channel_gram (Z : Matrix (Fin 2) (Fin 2) R) :
    Z * evenBlock 1 0 * Zᴴ = (Z * evenBlock 1 0) * (Z * evenBlock 1 0)ᴴ :=
  cut_channel_gram _ Z plus_cut_idempotent plus_cut_star

theorem minus_channel_gram (Z : Matrix (Fin 2) (Fin 2) R) :
    Z * evenBlock 0 1 * Zᴴ = (Z * evenBlock 0 1) * (Z * evenBlock 0 1)ᴴ :=
  cut_channel_gram _ Z minus_cut_idempotent minus_cut_star

theorem matrix_double_gram (Z : Matrix (Fin 2) (Fin 2) R) :
    Z * Zᴴ = (Z * evenBlock 1 0) * (Z * evenBlock 1 0)ᴴ +
      (Z * evenBlock 0 1) * (Z * evenBlock 0 1)ᴴ := by
  simpa only [plus_cut_complement, Matrix.star_eq_conjTranspose] using
    cut_double_gram (evenBlock 1 0) Z plus_cut_idempotent plus_cut_star

end MatrixChannels
end InfoGeometry.OperatorAlgebra.FreedDefectChannels
