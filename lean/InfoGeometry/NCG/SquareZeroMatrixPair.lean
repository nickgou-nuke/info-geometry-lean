/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.Canonical.DrazinMPCartan
import InfoGeometry.Algebra.PeirceRegularityIdentities
import InfoGeometry.NCG.NonCommutativeFredholmIndex

/-! # Universal and reflexive square-zero matrix pairs

The generators are arbitrary matrices. Square-zero hypotheses suffice for the
universal table; the last section explicitly adds the two reflexive equations.
-/
namespace InfoGeometry.NCG.SquareZeroMatrixPair

open NonCommutativeFredholmIndex
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R]
variable {X Y : Matrix n n R} (hX : X * X = 0) (hY : Y * Y = 0)

include hX hY

theorem sum_sq : (X + Y) * (X + Y) = anticommutator X Y := by
  simp only [anticommutator]
  noncomm_ring [hX, hY]

theorem difference_sq : (X - Y) * (X - Y) = -anticommutator X Y := by
  simp only [anticommutator]
  noncomm_ring [hX, hY]

theorem difference_mul_sum : (X - Y) * (X + Y) = commutator X Y := by
  simp only [NonCommutativeFredholmIndex.commutator]
  noncomm_ring [hX, hY]

theorem sum_mul_difference : (X + Y) * (X - Y) = -commutator X Y := by
  simp only [NonCommutativeFredholmIndex.commutator]
  noncomm_ring [hX, hY]

theorem sum_difference_anticommute : anticommutator (X + Y) (X - Y) = 0 := by
  rw [anticommutator, sum_mul_difference hX hY, difference_mul_sum hX hY, neg_add_cancel]

theorem commutator_mul_sum :
    commutator X Y * (X + Y) = X * Y * X - Y * X * Y := by
  simp only [NonCommutativeFredholmIndex.commutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem commutator_anticommutes_sum : anticommutator (commutator X Y) (X + Y) = 0 := by
  simp only [NonCommutativeFredholmIndex.commutator, anticommutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem commutator_anticommutes_difference :
    anticommutator (commutator X Y) (X - Y) = 0 := by
  simp only [NonCommutativeFredholmIndex.commutator, anticommutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem commutator_commutator_sum :
    commutator (commutator X Y) (X + Y) = 2 • (X * Y * X - Y * X * Y) := by
  simp only [NonCommutativeFredholmIndex.commutator, two_nsmul]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem commutator_mul_difference :
    commutator X Y * (X - Y) = (X + Y) * anticommutator X Y := by
  simp only [NonCommutativeFredholmIndex.commutator, anticommutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem anticommutator_commutes_sum : Commute (anticommutator X Y) (X + Y) := by
  rw [← sum_sq hX hY]
  exact mul_assoc _ _ _

theorem anticommutator_commutes_difference : Commute (anticommutator X Y) (X - Y) := by
  change anticommutator X Y * (X - Y) = (X - Y) * anticommutator X Y
  simp only [anticommutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem commutator_sq :
    commutator X Y * commutator X Y = anticommutator X Y * anticommutator X Y := by
  simp only [NonCommutativeFredholmIndex.commutator, anticommutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

theorem sum_cube : (X + Y) * (X + Y) * (X + Y) = X * Y * X + Y * X * Y := by
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y]

section Reflexive
variable (hXYX : X * Y * X = X) (hYXY : Y * X * Y = Y)
include hXYX hYXY

theorem sum_cube_of_reflexive : (X + Y) * (X + Y) * (X + Y) = X + Y := by
  rw [sum_cube hX hY, hXYX, hYXY]

theorem difference_cube_of_reflexive : (X - Y) * (X - Y) * (X - Y) = -(X - Y) := by
  have hxy : X * (Y * X) = X := by simpa only [mul_assoc] using hXYX
  have hyx : Y * (X * Y) = Y := by simpa only [mul_assoc] using hYXY
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y, hxy, hyx]

theorem commutator_cube_of_reflexive :
    commutator X Y * commutator X Y * commutator X Y = commutator X Y := by
  obtain ⟨hp, hq, hqp⟩ :=
    InfoGeometry.Canonical.DrazinMPCartan.reflexive_squareZero_supports hXYX hYXY hX
  have hpq : (X * Y) * (Y * X) = 0 := by
    calc
      _ = X * (Y * Y) * X := by simp only [mul_assoc]
      _ = 0 := by rw [hY, mul_zero, zero_mul]
  exact InfoGeometry.Algebra.PeirceRegularityIdentities.orthogonal_difference_cube
    hp.eq hq.eq hpq hqp

theorem commutator_mul_sum_of_reflexive : commutator X Y * (X + Y) = X - Y := by
  rw [commutator_mul_sum hX hY, hXYX, hYXY]

theorem commutator_mul_difference_of_reflexive : commutator X Y * (X - Y) = X + Y := by
  have hxy : X * (Y * X) = X := by simpa only [mul_assoc] using hXYX
  have hyx : Y * (X * Y) = Y := by simpa only [mul_assoc] using hYXY
  simp only [NonCommutativeFredholmIndex.commutator]
  noncomm_ring [hX, hY, ← mul_assoc X X, ← mul_assoc Y Y, hxy, hyx]

end Reflexive

omit hX hY in
/-- Opposite Peirce corners instantiate the universal pair without a chosen basis. -/
theorem corner_sum_cube {P : Matrix n n R} (hP : IsIdempotentElem P) (A B : Matrix n n R)
    (hABA : component10 P A * component01 P B * component10 P A = component10 P A)
    (hBAB : component01 P B * component10 P A * component01 P B = component01 P B) :
    (component10 P A + component01 P B) * (component10 P A + component01 P B) *
      (component10 P A + component01 P B) = component10 P A + component01 P B := by
  exact sum_cube_of_reflexive
    (peirce10_mul_peirce10_eq_zero P hP.eq (component10_mem P A) (component10_mem P A))
    (peirce01_mul_peirce01_eq_zero P hP.eq (component01_mem P B) (component01_mem P B)) hABA hBAB

end InfoGeometry.NCG.SquareZeroMatrixPair
