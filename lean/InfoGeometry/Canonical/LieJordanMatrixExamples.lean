/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanMatrixGeometry
import InfoGeometry.Core.PeirceStarCharges
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Noncommuting full-matrix witnesses

The general results retain arbitrary matrix size and arbitrary algebra inputs.
These three explicit complex matrices witness nonvanishing of the Lie–Jordan
correction and of the Peirce odd sector. The projection has every entry equal
to `1 / 3`, so it has nonzero off-diagonal entries in the displayed basis.
-/

namespace InfoGeometry.Canonical.LieJordanMatrixExamples

open scoped Matrix ComplexOrder

open InfoGeometry.Core.LieJordanComposition
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.OperatorCliffordDouble
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceStarCharges
open InfoGeometry.Canonical.LieJordanMatrixGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- A skew-Hermitian coefficient with every off-diagonal entry nonzero. -/
def H : Mat3 := !![0, 1, 2; -1, 0, 3; -2, -3, 0]

/-- A Hermitian coefficient whose commutator with `H` is nonzero. -/
def S : Mat3 := !![1, 2, 3; 2, 4, 5; 3, 5, 6]

/-- The orthogonal projection onto the line spanned by `(1,1,1)`. -/
def P : Mat3 := fun _ _ => (1 / 3 : ℂ)

theorem H_conjTranspose : Hᴴ = -H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Matrix.conjTranspose_apply]

theorem S_isSelfAdjoint : IsSelfAdjoint S := by
  change Sᴴ = S
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, Matrix.conjTranspose_apply]

theorem P_isStarProjection : IsStarProjection P := by
  constructor
  · change P * P = P
    ext i j
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]
  · change Pᴴ = P
    ext i j
    norm_num [P, Matrix.conjTranspose_apply]

theorem P_zero_one_ne_zero : P 0 1 ≠ 0 := by
  norm_num [P]

theorem H_S_commutator_zero_zero : (⁅H, S⁆ : Mat3) 0 0 = 16 := by
  change (H * S - S * H) 0 0 = 16
  norm_num [H, S, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_succ]

theorem H_S_not_commute : ¬ Commute H S := by
  intro hc
  have hz : (⁅H, S⁆ : Mat3) = 0 := sub_eq_zero.mpr hc.eq
  have he := congrArg (fun x : Mat3 => x 0 0) hz
  rw [H_S_commutator_zero_zero] at he
  norm_num at he

theorem H_mul_S_ne_S_mul_H : H * S ≠ S * H := by
  intro h
  exact H_S_not_commute h

/-- The actual endomorphisms of the full matrix space fail to commute. -/
theorem H_S_plus_minus_not_commute :
    ¬ Commute (plus (R := ℂ) H S) (minus (R := ℂ) H S) := by
  intro hc
  exact H_S_not_commute
    ((plus_minus_commute_iff matrix_doubling_injective H S).mp hc)

/-- The intake's reversed correction sign fails for these noncommuting matrices. -/
theorem H_S_wrong_ordered_product_ne :
    minus (R := ℂ) H S * plus (R := ℂ) H S ≠
      LieAlgebra.ad ℂ Mat3 H * LieAlgebra.ad ℂ Mat3 H -
        jordanLeft (R := ℂ) S * jordanLeft (R := ℂ) S -
          jordanLeft (R := ℂ) ⁅H, S⁆ := by
  intro h
  apply H_S_plus_minus_not_commute
  change plus (R := ℂ) H S * minus (R := ℂ) H S =
    minus (R := ℂ) H S * plus (R := ℂ) H S
  rw [plus_mul_minus]
  exact h.symm

/-- The bilinear trace quadratic form is not positive on all real-valued matrices. -/
theorem trace_H_square : Matrix.trace (H * H) = -28 := by
  norm_num [H, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Conjugate transpose gives the distinct, positive Gram expression. -/
theorem trace_H_gram : Matrix.trace (Hᴴ * H) = 28 := by
  rw [H_conjTranspose, neg_mul, Matrix.trace_neg, trace_H_square]
  norm_num

/-- Faithful lifting to the doubled matrix space preserves this obstruction. -/
theorem H_S_lifted_pair_not_commute :
    ¬ Commute (lift (plus (R := ℂ) H S)) (lift (minus (R := ℂ) H S)) := by
  intro hc
  exact H_S_not_commute ((lifted_pair_commute_iff H S).mp hc)

/-- The upper-right block of the doubled square contains a nonzero correction. -/
theorem H_S_doubled_pair_correction_ne_zero :
    upperRight (diracPlus (minus (R := ℂ) H S) (plus (R := ℂ) H S) ^ 2) ≠ 0 := by
  intro hz
  exact H_S_not_commute ((doubled_pair_upperRight_eq_zero_iff H S).mp hz)

theorem P_S_commutator_zero_one : (⁅P, S⁆ : Mat3) 0 1 = 5 / 3 := by
  change (P * S - S * P) 0 1 = 5 / 3
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  norm_num [P, S, Fin.sum_univ_succ]

theorem P_S_not_commute : ¬ Commute P S := by
  intro hc
  have hz : (⁅P, S⁆ : Mat3) = 0 := sub_eq_zero.mpr hc.eq
  have he := congrArg (fun x : Mat3 => x 0 1) hz
  rw [P_S_commutator_zero_one] at he
  norm_num at he

theorem P_S_odd_ne_zero : odd P S ≠ 0 := by
  intro hz
  exact P_S_not_commute
    ((odd_eq_zero_iff_commute P_isStarProjection.isIdempotentElem S).mp hz)

theorem P_S_imaginary_commutator_ne_zero :
    (Complex.I • ⁅P, S⁆ : Mat3) ≠ 0 := by
  intro hz
  have hb : (⁅P, S⁆ : Mat3) = 0 :=
    (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  exact P_S_not_commute (sub_eq_zero.mp hb)

theorem P_S_charges_isHermitian :
    (odd P S).IsHermitian ∧ (Complex.I • ⁅P, S⁆).IsHermitian :=
  ⟨(odd_isSelfAdjoint P_isStarProjection.isSelfAdjoint S_isSelfAdjoint).isHermitian,
    imaginary_commutator_isHermitian P_isStarProjection.isSelfAdjoint S_isSelfAdjoint⟩

theorem P_S_charges_equal_square :
    (Complex.I • ⁅P, S⁆) ^ 2 = (odd P S) ^ 2 :=
  imaginary_commutator_square P_isStarProjection.isIdempotentElem S

theorem P_S_common_square_posSemidef : ((odd P S) ^ 2).PosSemidef :=
  odd_square_posSemidef P_isStarProjection S_isSelfAdjoint

theorem P_S_charges_anticommute :
    odd P S * (Complex.I • ⁅P, S⁆) + (Complex.I • ⁅P, S⁆) * odd P S = 0 :=
  odd_imaginary_commutator_anticommute P_isStarProjection.isIdempotentElem S

end

end InfoGeometry.Canonical.LieJordanMatrixExamples
