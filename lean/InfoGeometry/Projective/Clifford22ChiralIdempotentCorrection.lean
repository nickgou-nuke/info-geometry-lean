/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Coordinate check for the split `Cl(2,2)` primitive idempotent

This owner checks the explicit four-generator matrix frame used in the
Clifford/twistor proposal. In that frame the sign in the proposed Fano product
matters: `(1 + ω) * (1 + E₂E₃)` is `4 E₁₁`, while `(1 + ω) * (1 - E₂E₃)` is
`4 E₀₀`. After division by four, both are primitive diagonal idempotents.

#### BUCKET 1: CLOSED FINITE THEOREMS
The matrix products and the normalized idempotent laws are proved over `ℝ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
These identities concern the displayed `4 × 4` representation only.

#### BUCKET 3: OPEN CLOSURE DEBT
This coordinate check does not prove the universal property of the Clifford
algebra, an algebra isomorphism with all of `M₄(ℝ)`, or an amplituhedron model.
-/

namespace InfoGeometry.Projective.Clifford22ChiralIdempotentCorrection

open Matrix

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- First generator in the displayed real split-Clifford matrix frame. -/
def e1 : Mat4 :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- Second generator in the displayed real split-Clifford matrix frame. -/
def e2 : Mat4 :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- Third generator in the displayed real split-Clifford matrix frame. -/
def e3 : Mat4 :=
  !![0, 0, 0, 1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

/-- Fourth generator in the displayed real split-Clifford matrix frame. -/
def e4 : Mat4 :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- Volume element in the explicit split-signature matrix frame. -/
def omega : Mat4 := e1 * e2 * e3 * e4

/-- The bivector `E₂E₃` in the same frame. -/
def e23 : Mat4 := e2 * e3

/-- The first diagonal matrix unit. -/
def e00 : Mat4 := Matrix.diagonal ![(1 : ℝ), 0, 0, 0]
/-- The second diagonal matrix unit. -/
def e11 : Mat4 := Matrix.diagonal ![0, (1 : ℝ), 0, 0]

/-- The quadratic form used as the scalar part of a bivector square. -/
def bivecNormI1 (p12 p13 p14 p23 p24 p34 : ℝ) : ℝ :=
  -p12 ^ 2 + p13 ^ 2 + p14 ^ 2 + p23 ^ 2 + p24 ^ 2 - p34 ^ 2

/-- The Klein/Plücker quadratic relation in the chosen six-coordinate order. -/
def plueckerRel (p12 p13 p14 p23 p24 p34 : ℝ) : ℝ :=
  p12 * p34 - p13 * p24 + p14 * p23

/-- Determinant of the first displayed generator. -/
private theorem e1_det : Matrix.det e1 = 1 := by
  norm_num [e1, Matrix.det_succ_row_zero, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Fin.succAbove]

/-- Determinant of the third displayed generator. -/
private theorem e3_det : Matrix.det e3 = 1 := by
  norm_num [e3, Matrix.det_succ_row_zero, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Fin.succAbove]

/-- A decomposable bivector need not have matrix rank two: in this explicit
Clifford frame, `E₁E₃` lies on the Plücker quadric, while its determinant is
one, so its represented `4 × 4` matrix is invertible. -/
theorem plucker_condition_does_not_force_singular_bivector :
    plueckerRel 0 1 0 0 0 0 = 0 ∧
      bivecNormI1 0 1 0 0 0 0 = 1 ∧ Matrix.det (e1 * e3) = 1 := by
  refine ⟨by norm_num [plueckerRel], by norm_num [bivecNormI1], ?_⟩
  rw [Matrix.det_mul, e1_det, e3_det]
  norm_num

/-- The explicit split-Clifford generators witness that the matrix carrier is
noncommutative. -/
theorem generators_do_not_commute : e1 * e2 ≠ e2 * e1 := by
  intro h
  have h01 := congrArg (fun M : Mat4 => M 0 1) h
  norm_num [e1, e2, Matrix.mul_apply, Fin.sum_univ_succ] at h01

/-- Diagonal form of the volume element in this specific matrix basis. -/
private theorem omega_diagonal :
    omega = Matrix.diagonal ![(1 : ℝ), 1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega, e1, e2, e3, e4, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Diagonal form of the bivector `e₂e₃` in this specific matrix basis. -/
private theorem e23_diagonal :
    e23 = Matrix.diagonal ![-(1 : ℝ), 1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e23, e2, e3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The plus-sign product selects the second diagonal primitive idempotent. -/
theorem plus_sign_product_eq_four_e11 :
    ((1 : Mat4) + omega) * ((1 : Mat4) + e23) = (4 : ℝ) • e11 := by
  rw [omega_diagonal, e23_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e11, Matrix.diagonal, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The minus-sign product selects the first diagonal primitive idempotent. -/
theorem minus_sign_product_eq_four_e00 :
    ((1 : Mat4) + omega) * ((1 : Mat4) - e23) = (4 : ℝ) • e00 := by
  rw [omega_diagonal, e23_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e00, Matrix.diagonal, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The sign-corrected plus product, normalized by four, is idempotent. -/
theorem plus_sign_normalized_idempotent :
    ((1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) + e23))) *
        ((1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) + e23))) =
      (1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) + e23)) := by
  rw [plus_sign_product_eq_four_e11]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e11, Matrix.diagonal, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The sign-corrected minus product, normalized by four, is idempotent. -/
theorem minus_sign_normalized_idempotent :
    ((1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) - e23))) *
        ((1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) - e23))) =
      (1 / 4 : ℝ) • (((1 : Mat4) + omega) * ((1 : Mat4) - e23)) := by
  rw [minus_sign_product_eq_four_e00]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e00, Matrix.diagonal, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_succ]

end InfoGeometry.Projective.Clifford22ChiralIdempotentCorrection
