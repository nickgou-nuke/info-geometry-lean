/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# Coefficient audit for five graded operator components

The statements below hold for arbitrary operator values in an associative ring.
They audit the integer coefficient identities independently of any claim that a
particular charge map has the asserted five eigencomponents.
-/

namespace InfoGeometry.OperatorAlgebra.FiveGradeCoefficientAudit

variable {B : Type*} [Ring B]

def delta0 (m2 m1 z p1 p2 : B) : B := m2 + m1 + z + p1 + p2
def delta1 (m2 m1 p1 p2 : B) : B := -((2 : ℤ) • m2) - m1 + p1 + (2 : ℤ) • p2
def delta2 (m2 m1 p1 p2 : B) : B := (4 : ℤ) • m2 + m1 + p1 + (4 : ℤ) • p2
def delta3 (m2 m1 p1 p2 : B) : B := -((8 : ℤ) • m2) - m1 + p1 + (8 : ℤ) • p2
def delta4 (m2 m1 p1 p2 : B) : B := (16 : ℤ) • m2 + m1 + p1 + (16 : ℤ) • p2
def delta5 (m2 m1 p1 p2 : B) : B := -((32 : ℤ) • m2) - m1 + p1 + (32 : ℤ) • p2

/-- The five-charge polynomial annihilates the total component. -/
theorem fifth_order_relation (m2 m1 _z p1 p2 : B) :
    delta5 m2 m1 p1 p2 - (5 : ℤ) • delta3 m2 m1 p1 p2 +
      (4 : ℤ) • delta1 m2 m1 p1 p2 = 0 := by
  simp only [delta1, delta3, delta5]
  abel

/-- The even polynomial isolates grade zero, with factor four. -/
theorem isolate_grade_zero (m2 m1 z p1 p2 : B) :
    delta4 m2 m1 p1 p2 - (5 : ℤ) • delta2 m2 m1 p1 p2 +
      (4 : ℤ) • delta0 m2 m1 z p1 p2 = (4 : ℤ) • z := by
  simp only [delta0, delta2, delta4]
  abel

/-- Correct integer combination isolating the positive grade-one component. -/
theorem isolate_grade_plus_one (m2 m1 p1 p2 : B) :
    (16 : ℤ) • delta2 m2 m1 p1 p2 - (4 : ℤ) • delta4 m2 m1 p1 p2 +
      (16 : ℤ) • delta1 m2 m1 p1 p2 - (4 : ℤ) • delta3 m2 m1 p1 p2 =
        (24 : ℤ) • p1 := by
  simp only [delta1, delta2, delta3, delta4]
  abel

/-- Correct integer combination isolating the negative grade-one component. -/
theorem isolate_grade_minus_one (m2 m1 p1 p2 : B) :
    (16 : ℤ) • delta2 m2 m1 p1 p2 - (4 : ℤ) • delta4 m2 m1 p1 p2 -
      ((16 : ℤ) • delta1 m2 m1 p1 p2 - (4 : ℤ) • delta3 m2 m1 p1 p2) =
        (24 : ℤ) • m1 := by
  simp only [delta1, delta2, delta3, delta4]
  abel

/-- Correct integer combination isolating the positive grade-two component. -/
theorem isolate_grade_plus_two (m2 m1 p1 p2 : B) :
    delta4 m2 m1 p1 p2 - delta2 m2 m1 p1 p2 +
      (2 : ℤ) • (delta3 m2 m1 p1 p2 - delta1 m2 m1 p1 p2) =
        (24 : ℤ) • p2 := by
  simp only [delta1, delta2, delta3, delta4]
  abel

/-- Correct integer combination isolating the negative grade-two component. -/
theorem isolate_grade_minus_two (m2 m1 p1 p2 : B) :
    delta4 m2 m1 p1 p2 - delta2 m2 m1 p1 p2 -
      (2 : ℤ) • (delta3 m2 m1 p1 p2 - delta1 m2 m1 p1 p2) =
        (24 : ℤ) • m2 := by
  simp only [delta1, delta2, delta3, delta4]
  abel

/-- The grade-one sum expression cancels both grade-two components. -/
theorem claimed_grade_one_sum_coefficients (m2 m1 p1 p2 : B) :
    (4 : ℤ) • delta2 m2 m1 p1 p2 - delta4 m2 m1 p1 p2 =
      (3 : ℤ) • (m1 + p1) := by
  simp only [delta2, delta4]
  abel

/-- An off-diagonal matrix-unit counterexample to the claimed grade-one sum. -/
def e01 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

theorem claimed_grade_one_sum_is_not_universal :
    ¬ ∀ (m2 m1 p1 p2 : Matrix (Fin 2) (Fin 2) ℤ),
      (4 : ℤ) • delta2 m2 m1 p1 p2 - delta4 m2 m1 p1 p2 =
        (12 : ℤ) • (m2 + p2) := by
  intro h
  have hbad := h 0 e01 0 0
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hbad
  simp only [delta2, delta4, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.zero_apply] at hentry
  norm_num [e01] at hentry

end InfoGeometry.OperatorAlgebra.FiveGradeCoefficientAudit
