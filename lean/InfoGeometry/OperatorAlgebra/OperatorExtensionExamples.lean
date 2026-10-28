/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixCayleyGeometry

/-!
# Nondiagonal, noncommuting witnesses for the operator extensions

The projections act on a three-dimensional space. Their chiral square is
nondiagonal and nonzero, but has a nontrivial kernel. The same projections
give noncommuting Maurer--Cartan directions and a unitary Cayley image that
does not commute with the original projection.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorExtensionExamples

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open PeirceChiralGeometry MatrixMaurerCartan MatrixCayleyGeometry
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ

def P : Mat := !![1 / 9, 2 / 9, 2 / 9; 2 / 9, 4 / 9, 4 / 9; 2 / 9, 4 / 9, 4 / 9]

def Q : Mat := !![4 / 9, 2 / 9, 4 / 9; 2 / 9, 1 / 9, 2 / 9; 4 / 9, 2 / 9, 4 / 9]

theorem P_isStarProjection : IsStarProjection P := by
  constructor
  · change P * P = P
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]
  · change star P = P
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.star_apply]

theorem Q_isStarProjection : IsStarProjection Q := by
  constructor
  · change Q * Q = Q
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, Matrix.mul_apply, Fin.sum_univ_succ]
  · change star Q = Q
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, Matrix.star_apply]

theorem lie_P_Q_entry : (⁅P, Q⁆ : Mat) 0 1 = (-8 / 27 : ℂ) := by
  norm_num [Ring.lie_def, P, Q, Matrix.mul_apply, Fin.sum_univ_succ]

theorem P_Q_not_commute : ¬ Commute P Q := by
  intro h
  have hz : (⁅P, Q⁆ : Mat) 0 1 = 0 := by
    change (P * Q - Q * P) 0 1 = 0
    rw [h.eq, sub_self]
    rfl
  rw [lie_P_Q_entry] at hz
  norm_num at hz

theorem oddPart_P_Q : oddPart P Q =
    !![160 / 729, 104 / 729, 176 / 729;
       104 / 729, -224 / 729, -80 / 729;
       176 / 729, -80 / 729, 64 / 729] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddPart, component10, component01, complementIdempotent,
      P, Q, Matrix.mul_apply, Fin.sum_univ_succ]

theorem component10_P_Q : component10 P Q =
    !![80 / 729, -56 / 729, 16 / 729;
       160 / 729, -112 / 729, 32 / 729;
       160 / 729, -112 / 729, 32 / 729] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [component10, complementIdempotent, P, Q,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem chiral_square_matrix : oddPart P Q * oddPart P Q =
    !![832 / 6561, -256 / 6561, 128 / 2187;
       -256 / 6561, 832 / 6561, 128 / 2187;
       128 / 2187, 128 / 2187, 512 / 6561] := by
  rw [oddPart_P_Q]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem chiral_square_posSemidef : (oddPart P Q * oddPart P Q).PosSemidef :=
  odd_square_posSemidef P_isStarProjection Q_isStarProjection.isSelfAdjoint

theorem chiral_square_ne_zero : oddPart P Q * oddPart P Q ≠ 0 := by
  intro h
  exact P_Q_not_commute ((odd_square_eq_zero_iff_commute
    P_isStarProjection Q_isStarProjection.isSelfAdjoint).mp h)

/-- A nonzero off-diagonal entry rules out every scalar matrix. -/
theorem chiral_square_not_scalar (z : ℂ) : oddPart P Q * oddPart P Q ≠ z • (1 : Mat) := by
  intro h
  have he := congrArg (fun A : Mat => A 0 1) h
  rw [chiral_square_matrix] at he
  norm_num at he

theorem chiral_square_kernel :
    (oddPart P Q * oddPart P Q) *ᵥ (![2, 2, -3] : Fin 3 → ℂ) = 0 := by
  rw [chiral_square_matrix]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Positive definiteness is false even though this square is nonzero. -/
theorem chiral_square_not_posDef : ¬ (oddPart P Q * oddPart P Q).PosDef := by
  intro h
  have hw : (![2, 2, -3] : Fin 3 → ℂ) ≠ 0 := by
    intro hz
    have he := congrFun hz 0
    norm_num at he
  have hpos := h.dotProduct_mulVec_pos hw
  rw [chiral_square_kernel] at hpos
  simp at hpos

/-- A native unit with a full nondiagonal square-zero corner as its increment. -/
def unipotentFrame : Matˣ where
  val := 1 + component10 P Q
  inv := 1 - component10 P Q
  val_inv := by
    have hN := (corners_square_zero P_isStarProjection.isIdempotentElem Q).1
    noncomm_ring [hN]
  inv_val := by
    have hN := (corners_square_zero P_isStarProjection.isIdempotentElem Q).1
    noncomm_ring [hN]

/-- The direction-bracket correction in Maurer--Cartan is actually nonzero. -/
theorem maurerCartan_direction_term_ne_zero :
    maurerCartan unipotentFrame ⁅P, Q⁆ ≠ 0 := by
  intro h
  rw [maurerCartan_apply_conj] at h
  have he := congrArg (fun A : Mat => A 0 0) h
  change (((1 - component10 P Q) * ⁅P, Q⁆ *
    (1 + component10 P Q) - ⁅P, Q⁆) 0 0) = 0 at he
  rw [component10_P_Q] at he
  norm_num [Ring.lie_def, P, Q, Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- Dropping the direction term changes a zero-curvature identity into a false assertion. -/
theorem maurerCartan_without_direction_term_ne_zero :
    ⁅P, maurerCartan unipotentFrame Q⁆ - ⁅Q, maurerCartan unipotentFrame P⁆ +
      ⁅maurerCartan unipotentFrame P, maurerCartan unipotentFrame Q⁆ ≠ 0 := by
  have h := maurerCartan_equation unipotentFrame P Q
  have he : ⁅P, maurerCartan unipotentFrame Q⁆ - ⁅Q, maurerCartan unipotentFrame P⁆ +
      ⁅maurerCartan unipotentFrame P, maurerCartan unipotentFrame Q⁆ =
      maurerCartan unipotentFrame ⁅P, Q⁆ := by
    apply sub_eq_zero.mp
    convert h using 1 <;> abel
  rw [he]
  exact maurerCartan_direction_term_ne_zero

theorem cayley_lie_mem_unitary : cayley ⁅P, Q⁆ ∈ unitary Mat :=
  cayley_mem_unitary_of_skew (MatrixOperatorIdentities.star_lie_of_isSelfAdjoint
    P_isStarProjection.isSelfAdjoint Q_isStarProjection.isSelfAdjoint)

/-- The unitary Cayley image still fails to commute with the projection. -/
theorem cayley_lie_not_commute : ¬ Commute P (cayley ⁅P, Q⁆) := by
  have hJ := MatrixOperatorIdentities.star_lie_of_isSelfAdjoint
    P_isStarProjection.isSelfAdjoint Q_isStarProjection.isSelfAdjoint
  let _ := (isUnit_one_sub_and_one_add_of_skew hJ).2.invertible
  intro h
  have hc := (commute_cayley_iff P ⁅P, Q⁆).mp h
  have hz : oddPart P Q = 0 := by
    rw [odd_eq_double_commutator P_isStarProjection.isIdempotentElem]
    change P * ⁅P, Q⁆ - ⁅P, Q⁆ * P = 0
    exact sub_eq_zero.mpr hc.eq
  exact P_Q_not_commute ((odd_zero_iff_commute P_isStarProjection.isIdempotentElem Q).mp hz)

end InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
