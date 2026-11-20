/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A regular contrast with a degenerate mixed derivative away from the diagonal

The supplied literature map asserts that an arbitrary divergence induces a
para-Kähler metric on the whole product. This explicit real counterexample
isolates the missing global nondegeneracy hypothesis. For `s = x - y`, set

`D(x,y) = s^6 - 3*s^4 + 3*s^2`.

It is smooth, nonnegative, and vanishes precisely when `x = y`. Both first
partial derivatives vanish on the diagonal. The negative mixed derivative,
defined using Mathlib's actual `deriv`, is `6*(5*s^2 - 1)*(s^2 - 1)`. It equals
`6` on the diagonal but vanishes at the off-diagonal point `(1,0)`.

The carrier is the real line, so the mixed Hessian has one coefficient. This
file does not construct a manifold, a para-Kähler structure, or a matrix
substitute for a noncommutative theorem. It proves the obstruction to extending
diagonal regularity to global mixed-Hessian nondegeneracy. The separate owner
`Geometry.ParaHessianMixedPotential` concerns a different, quadratic potential.
-/

noncomputable section

namespace InfoGeometry.Geometry.DivergenceMixedHessianCounterexample

open scoped ContDiff

/-- A polynomial contrast depending on the difference of its two arguments. -/
def divergence (x y : ℝ) : ℝ :=
  (x - y) ^ 6 - 3 * (x - y) ^ 4 + 3 * (x - y) ^ 2

/-- A sum-of-squares factorization establishes the sign and the zero set. -/
theorem divergence_factorization (x y : ℝ) :
    divergence x y =
      (x - y) ^ 2 * (((x - y) ^ 2 - (3 / 2 : ℝ)) ^ 2 + 3 / 4) := by
  unfold divergence
  ring

theorem divergence_nonneg (x y : ℝ) : 0 ≤ divergence x y := by
  rw [divergence_factorization]
  exact mul_nonneg (sq_nonneg (x - y))
    (add_nonneg (sq_nonneg _) (by norm_num))

theorem divergence_pos_of_ne {x y : ℝ} (hxy : x ≠ y) :
    0 < divergence x y := by
  rw [divergence_factorization]
  exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (by norm_num))

@[simp] theorem divergence_self (x : ℝ) : divergence x x = 0 := by
  simp [divergence]

theorem divergence_eq_zero_iff (x y : ℝ) : divergence x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    exact (ne_of_gt (divergence_pos_of_ne hxy)) h
  · rintro rfl
    exact divergence_self x

/-- The contrast is smooth jointly in both real arguments. -/
theorem contDiff_divergence :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => divergence p.1 p.2) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 - p.2) :=
    contDiff_fst.sub contDiff_snd
  exact ((hs.pow 6).sub (contDiff_const.mul (hs.pow 4))).add
    (contDiff_const.mul (hs.pow 2))

/-- The genuine derivative with respect to the first argument. -/
theorem hasDerivAt_divergence_left (x y : ℝ) :
    HasDerivAt (fun t => divergence t y)
      (6 * (x - y) ^ 5 - 12 * (x - y) ^ 3 + 6 * (x - y)) x := by
  have hs : HasDerivAt (fun t : ℝ => t - y) 1 x :=
    (hasDerivAt_id x).sub_const y
  unfold divergence
  convert ((hs.pow 6).sub ((hs.pow 4).const_mul 3)).add
    ((hs.pow 2).const_mul 3) using 1
  norm_num
  ring

/-- The genuine derivative with respect to the second argument. -/
theorem hasDerivAt_divergence_right (x y : ℝ) :
    HasDerivAt (divergence x)
      (-6 * (x - y) ^ 5 + 12 * (x - y) ^ 3 - 6 * (x - y)) y := by
  have hs : HasDerivAt (fun t : ℝ => x - t) (-1) y :=
    (hasDerivAt_id y).const_sub x
  unfold divergence
  convert ((hs.pow 6).sub ((hs.pow 4).const_mul 3)).add
    ((hs.pow 2).const_mul 3) using 1
  norm_num
  ring

theorem deriv_divergence_left (x y : ℝ) :
    deriv (fun t => divergence t y) x =
      6 * (x - y) ^ 5 - 12 * (x - y) ^ 3 + 6 * (x - y) :=
  (hasDerivAt_divergence_left x y).deriv

theorem deriv_divergence_right (x y : ℝ) :
    deriv (divergence x) y =
      -6 * (x - y) ^ 5 + 12 * (x - y) ^ 3 - 6 * (x - y) :=
  (hasDerivAt_divergence_right x y).deriv

@[simp] theorem deriv_divergence_left_self (x : ℝ) :
    deriv (fun t => divergence t x) x = 0 := by
  simp [deriv_divergence_left]

@[simp] theorem deriv_divergence_right_self (x : ℝ) :
    deriv (divergence x) x = 0 := by
  simp [deriv_divergence_right]

/-- Differentiating the actual right derivative in the left argument. -/
theorem hasDerivAt_deriv_divergence_right (x y : ℝ) :
    HasDerivAt (fun t => deriv (divergence t) y)
      (-6 * (5 * (x - y) ^ 2 - 1) * ((x - y) ^ 2 - 1)) x := by
  simp_rw [deriv_divergence_right]
  have hs : HasDerivAt (fun t : ℝ => t - y) 1 x :=
    (hasDerivAt_id x).sub_const y
  convert (((hs.pow 5).const_mul (-6)).add
    ((hs.pow 3).const_mul 12)).sub (hs.const_mul 6) using 1
  norm_num
  ring

/-- The negative mixed derivative, with the right derivative taken first. -/
def mixedHessian (x y : ℝ) : ℝ :=
  -deriv (fun t => deriv (divergence t) y) x

theorem mixedHessian_eq (x y : ℝ) :
    mixedHessian x y = 6 * (5 * (x - y) ^ 2 - 1) * ((x - y) ^ 2 - 1) := by
  rw [mixedHessian, (hasDerivAt_deriv_divergence_right x y).deriv]
  ring

@[simp] theorem mixedHessian_self (x : ℝ) : mixedHessian x x = 6 := by
  rw [mixedHessian_eq]
  norm_num

theorem mixedHessian_diagonal_pos (x : ℝ) : 0 < mixedHessian x x := by
  rw [mixedHessian_self]
  norm_num

theorem mixedHessian_one_zero : mixedHessian 1 0 = 0 := by
  rw [mixedHessian_eq]
  norm_num

/-- Diagonal regularity does not extend to global mixed nondegeneracy. -/
theorem not_forall_mixedHessian_ne_zero :
    ¬ ∀ x y : ℝ, mixedHessian x y ≠ 0 := by
  intro h
  exact h 1 0 mixedHessian_one_zero

end InfoGeometry.Geometry.DivergenceMixedHessianCounterexample
