/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixConservation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommuting quadratic invariant with nonzero off-diagonal entries

Three explicit nondiagonal Hermitian matrices satisfy a skew coefficient Lie
action. Their quadratic sum belongs to their native family centralizer and
is both nondiagonal and nonscalar. Centrality is relative to this family.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixCasimirExamples

open Matrix
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ

/-- An explicit Hermitian generator family in the full complex matrix algebra. -/
def H : Fin 3 → Mat :=
  ![!![-56 / 81, 23 / 81, -40 / 81;
        23 / 81, -8 / 81, 28 / 81;
        -40 / 81, 28 / 81, 64 / 81],
    !![0, Complex.I / 9, 8 * Complex.I / 9;
        -Complex.I / 9, 0, -4 * Complex.I / 9;
        -8 * Complex.I / 9, 4 * Complex.I / 9, 0],
    !![11 / 27, -8 / 27, -20 / 27;
        -8 / 27, 5 / 27, 8 / 27;
        -20 / 27, 8 / 27, -16 / 27]]

/-- The structure coefficients of the inner actions on the three generators. -/
def c : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![!![0, 0, 0; 0, 0, 2 * Complex.I; 0, -2 * Complex.I, 0],
    !![0, 0, -2 * Complex.I; 0, 0, 0; 2 * Complex.I, 0, 0],
    !![0, 2 * Complex.I, 0; -2 * Complex.I, 0, 0; 0, 0, 0]]

theorem c_skew (k i j : Fin 3) : c k i j = -c k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [c, Complex.ext_iff]

theorem H_isSelfAdjoint (k : Fin 3) : IsSelfAdjoint (H k) := by
  change star (H k) = H k
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [H, Matrix.star_apply, Complex.star_def, Complex.ext_iff,
      Complex.div_re, Complex.div_im]

theorem H_not_isDiag (k : Fin 3) : ¬ (H k).IsDiag := by
  intro h
  have hz : H k 0 1 = 0 := h (by decide)
  fin_cases k <;>
    norm_num [H, Complex.ext_iff, Complex.div_re, Complex.div_im] at hz

theorem lie_H_zero_one : ⁅H 0, H 1⁆ = (2 * Complex.I) • H 2 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, smul_eq_mul, Complex.ext_iff,
      Complex.div_re, Complex.div_im]

theorem lie_H_one_two : ⁅H 1, H 2⁆ = (2 * Complex.I) • H 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, smul_eq_mul, Complex.ext_iff,
      Complex.div_re, Complex.div_im]

theorem lie_H_two_zero : ⁅H 2, H 0⁆ = (2 * Complex.I) • H 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, smul_eq_mul, Complex.ext_iff,
      Complex.div_re, Complex.div_im]

/-- Every generator acts by the displayed skew coefficient matrix. -/
theorem bracket_action (k i : Fin 3) : ⁅H k, H i⁆ = ∑ j, c k i j • H j := by
  have h10 : ⁅H 1, H 0⁆ = -(2 * Complex.I) • H 2 := by
    rw [← lie_skew, lie_H_zero_one, neg_smul]
  have h21 : ⁅H 2, H 1⁆ = -(2 * Complex.I) • H 0 := by
    rw [← lie_skew, lie_H_one_two, neg_smul]
  have h02 : ⁅H 0, H 2⁆ = -(2 * Complex.I) • H 1 := by
    rw [← lie_skew, lie_H_two_zero, neg_smul]
  fin_cases k <;> fin_cases i <;>
    simp [c, Fin.sum_univ_succ, lie_H_zero_one, lie_H_one_two,
      lie_H_two_zero, h10, h21, h02]

theorem H_zero_one_not_commute : ¬ Commute (H 0) (H 1) := by
  intro h
  have hz : ⁅H 0, H 1⁆ = 0 := by
    change H 0 * H 1 - H 1 * H 0 = 0
    exact sub_eq_zero.mpr h.eq
  rw [lie_H_zero_one] at hz
  have him := congrArg (fun A : Mat => (A 0 0).im) hz
  norm_num [H, Matrix.smul_apply, smul_eq_mul,
    Complex.div_re, Complex.div_im] at him

/-- The quadratic element associated to this generator family. -/
def C : Mat := ∑ i, H i * H i

theorem C_mem_centralizer : C ∈ Subalgebra.centralizer ℂ (Set.range H) := by
  exact MatrixConservation.quadratic_sum_mem_centralizer H c bracket_action c_skew

theorem C_eq : C =
    !![65 / 27, -32 / 27, 4 / 27;
       -32 / 27, 17 / 27, 8 / 27;
       4 / 27, 8 / 27, 80 / 27] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C, H, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.ext_iff, Complex.div_re, Complex.div_im]

theorem C_zero_one_ne_zero : C 0 1 ≠ 0 := by
  rw [C_eq]
  norm_num

theorem C_not_isDiag : ¬ C.IsDiag := by
  intro h
  exact C_zero_one_ne_zero (h (by decide))

theorem C_ne_smul_one (z : ℂ) : C ≠ z • (1 : Mat) := by
  intro h
  apply C_zero_one_ne_zero
  have h01 := congrArg (fun A : Mat => A 0 1) h
  simpa [Matrix.smul_apply, Matrix.one_apply] using h01

end InfoGeometry.OperatorAlgebra.MatrixCasimirExamples
