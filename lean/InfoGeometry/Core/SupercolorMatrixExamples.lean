/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SupercolorMultiplication
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Concrete finite color systems

Matrix units on `Option ι` give distinct targets with a common source `none`.
Their color products genuinely mix colors. This is a supercolor system, not
the stronger disjoint-support system. No Lie-superalgebra classification is
claimed.
-/

namespace InfoGeometry.Core.SupercolorMatrixExamples

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.SuperGrassmannianSusy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Arrow from the common reference coordinate to color `i`. -/
def forward (i : ι) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.single (some i) none 1

/-- The transpose arrow from color `i` to the reference coordinate. -/
def backward (i : ι) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.single none (some i) 1

omit [Fintype ι] in
theorem backward_eq_star_forward (i : ι) : backward i = star (forward i) := by
  change _ = (forward i).conjTranspose
  simp [forward, backward]

theorem matrix_supercolor : IsSupercolorSystem (forward (ι := ι)) backward where
  mp i := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [forward, backward]
    · simp [forward, backward]
    · change ((forward i * backward i).conjTranspose) = _
      simp [forward, backward]
    · change ((backward i * forward i).conjTranspose) = _
      simp [forward, backward]
  d_mul_d i j := by
    exact Matrix.single_mul_single_of_ne 1 _ _ _ (by simp) 1
  b_mul_b i j := by
    exact Matrix.single_mul_single_of_ne 1 _ _ _ (by simp) 1
  b_mul_d_ne := by
    intro i j hij
    exact Matrix.single_mul_single_of_ne 1 _ _ _ (by simpa using hij) 1

/-- Unlike disjoint-support systems, off-diagonal color products are nonzero. -/
theorem colorBoson_eq_single (i j : ι) :
    colorBoson forward backward i j = Matrix.single (some i) (some j) 1 := by
  simp [colorBoson, forward, backward]

theorem colorBoson_ne_zero (i j : ι) : colorBoson forward backward i j ≠ 0 := by
  rw [colorBoson_eq_single]
  intro hz
  have hentry := congrArg (fun M => M (some i) (some j)) hz
  norm_num at hentry

/-- Concrete multiplication, including the matching-middle case. -/
theorem colorBoson_mul (i j l m : ι) :
    colorBoson forward backward i j * colorBoson forward backward l m =
      if j = l then colorBoson forward backward i m else 0 := by
  apply colorBoson_mul_of_common_source matrix_supercolor
    (q := Matrix.single none none 1)
  intro a
  simp [forward, backward]

example : IsSupercolorSystem (forward (ι := Fin 2)) backward := matrix_supercolor
example : IsSupercolorSystem (forward (ι := Fin 4)) backward := matrix_supercolor

example : colorBoson (forward (ι := Fin 2)) backward 0 1 *
    colorBoson forward backward 1 0 = colorBoson forward backward 0 0 := by
  simp [colorBoson_mul]

example : colorBoson (forward (ι := Fin 4)) backward 0 1 *
    colorBoson forward backward 2 3 = 0 := by
  simp [colorBoson_mul]

example : star (colorBoson (forward (ι := Fin 2)) backward 0 1) =
    colorBoson forward backward 1 0 :=
  star_colorBoson_of_dual backward_eq_star_forward 0 1

example : star (majoranaMinus (forward (0 : Fin 4)) (backward 0)) =
    -majoranaMinus (forward (0 : Fin 4)) (backward 0) :=
  star_majoranaMinus_of_dual backward_eq_star_forward 0

end InfoGeometry.Core.SupercolorMatrixExamples
