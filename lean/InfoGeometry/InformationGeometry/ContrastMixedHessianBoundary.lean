/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.MixedPairingNondegeneracy
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# A regular diagonal contrast with a degenerate mixed metric away from the diagonal

The polynomial `D(x,y) = (x-y)^6 - 3(x-y)^4 + 3(x-y)^2` is smooth,
nonnegative and zero exactly on the diagonal. Its first derivatives vanish
there, and its negative mixed derivative on the diagonal is `6`.
At `(1,0)` that same actual mixed derivative vanishes.

The associated doubled form is the native pullback from
`MixedPairingNondegeneracy`, and an explicit nonzero vector lies in its
radical at `(1,0)`. The example separates diagonal regularity from global
mixed nondegeneracy. No global para-Kähler or curvature claim is made.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.ContrastMixedHessianBoundary

open InfoGeometry.Geometry.MixedPairingNondegeneracy

/-- A real polynomial contrast on the full product `ℝ × ℝ`. -/
def contrast (x y : ℝ) : ℝ :=
  (x - y) ^ 6 - 3 * (x - y) ^ 4 + 3 * (x - y) ^ 2

theorem contDiff_contrast :
    ContDiff ℝ ⊤ (fun X : ℝ × ℝ => contrast X.1 X.2) := by
  unfold contrast
  fun_prop

theorem contrast_factorization (x y : ℝ) :
    contrast x y =
      (x - y) ^ 2 * (((x - y) ^ 2 - (3 / 2 : ℝ)) ^ 2 + 3 / 4) := by
  unfold contrast
  ring

@[simp] theorem contrast_diagonal (x : ℝ) : contrast x x = 0 := by
  simp [contrast]

theorem contrast_nonneg (x y : ℝ) : 0 ≤ contrast x y := by
  rw [contrast_factorization]
  positivity

theorem contrast_pos_of_ne {x y : ℝ} (hxy : x ≠ y) : 0 < contrast x y := by
  rw [contrast_factorization]
  exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)) (by positivity)

theorem contrast_eq_zero_iff (x y : ℝ) : contrast x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    exact (ne_of_gt (contrast_pos_of_ne hxy)) h
  · rintro rfl
    exact contrast_diagonal x

/-- Literal derivative in the first argument. -/
theorem hasDerivAt_contrast_left (x y : ℝ) :
    HasDerivAt (fun a => contrast a y)
      (6 * (x - y) ^ 5 - 12 * (x - y) ^ 3 + 6 * (x - y)) x := by
  have hs : HasDerivAt (fun a : ℝ => a - y) 1 x := by
    exact (hasDerivAt_id' x).sub_const y
  have h := ((hs.pow 6).sub ((hs.pow 4).const_mul 3)).add
    ((hs.pow 2).const_mul 3)
  change HasDerivAt
    (fun a : ℝ => (a - y) ^ 6 - 3 * (a - y) ^ 4 + 3 * (a - y) ^ 2)
    (6 * (x - y) ^ 5 - 12 * (x - y) ^ 3 + 6 * (x - y)) x
  convert h using 1
  ring

/-- Literal derivative in the second argument. -/
theorem hasDerivAt_contrast_right (x y : ℝ) :
    HasDerivAt (contrast x)
      (-6 * (x - y) ^ 5 + 12 * (x - y) ^ 3 - 6 * (x - y)) y := by
  have hs : HasDerivAt (fun b : ℝ => x - b) (-1) y := by
    exact (hasDerivAt_id' y).const_sub x
  have h := ((hs.pow 6).sub ((hs.pow 4).const_mul 3)).add
    ((hs.pow 2).const_mul 3)
  change HasDerivAt
    (fun b : ℝ => (x - b) ^ 6 - 3 * (x - b) ^ 4 + 3 * (x - b) ^ 2)
    (-6 * (x - y) ^ 5 + 12 * (x - y) ^ 3 - 6 * (x - y)) y
  convert h using 1
  ring

theorem deriv_contrast_left (x y : ℝ) :
    deriv (fun a => contrast a y) x =
      6 * (x - y) ^ 5 - 12 * (x - y) ^ 3 + 6 * (x - y) :=
  (hasDerivAt_contrast_left x y).deriv

theorem deriv_contrast_right (x y : ℝ) :
    deriv (contrast x) y =
      -6 * (x - y) ^ 5 + 12 * (x - y) ^ 3 - 6 * (x - y) :=
  (hasDerivAt_contrast_right x y).deriv

@[simp] theorem deriv_contrast_left_diagonal (x : ℝ) :
    deriv (fun a => contrast a x) x = 0 := by
  simp [deriv_contrast_left]

@[simp] theorem deriv_contrast_right_diagonal (x : ℝ) :
    deriv (contrast x) x = 0 := by
  simp [deriv_contrast_right]

/-- The first-variable derivative of the actual second-variable derivative. -/
theorem hasDerivAt_deriv_contrast_right (x y : ℝ) :
    HasDerivAt (fun a => deriv (contrast a) y)
      (-6 * (5 * (x - y) ^ 4 - 6 * (x - y) ^ 2 + 1)) x := by
  have hs : HasDerivAt (fun a : ℝ => a - y) 1 x := by
    exact (hasDerivAt_id' x).sub_const y
  have h := (((hs.pow 5).const_mul (-6)).add ((hs.pow 3).const_mul 12)).sub
    (hs.const_mul 6)
  have hfun : (fun a => deriv (contrast a) y) =
      (fun a : ℝ => -6 * (a - y) ^ 5 + 12 * (a - y) ^ 3 - 6 * (a - y)) := by
    funext a
    exact deriv_contrast_right a y
  rw [hfun]
  convert h using 1
  ring

/-- The coefficient is defined using native nested derivatives, not a supplied
polynomial value. -/
def mixedCoefficient (x y : ℝ) : ℝ :=
  -deriv (fun a => deriv (contrast a) y) x

theorem mixedCoefficient_eq (x y : ℝ) :
    mixedCoefficient x y =
      6 * (5 * (x - y) ^ 4 - 6 * (x - y) ^ 2 + 1) := by
  unfold mixedCoefficient
  rw [(hasDerivAt_deriv_contrast_right x y).deriv]
  ring

@[simp] theorem mixedCoefficient_diagonal (x : ℝ) :
    mixedCoefficient x x = 6 := by
  simp [mixedCoefficient_eq]

theorem mixedCoefficient_diagonal_pos (x : ℝ) : 0 < mixedCoefficient x x := by
  rw [mixedCoefficient_diagonal]
  norm_num

@[simp] theorem mixedCoefficient_one_zero : mixedCoefficient 1 0 = 0 := by
  norm_num [mixedCoefficient_eq]

/-- The actual mixed derivative multiplies the native real multiplication pairing. -/
def mixedPairing (x y : ℝ) : LinearMap.BilinForm ℝ ℝ :=
  mixedCoefficient x y • LinearMap.mul ℝ ℝ

@[simp] theorem mixedPairing_apply (x y u v : ℝ) :
    mixedPairing x y u v = mixedCoefficient x y * u * v := by
  change mixedCoefficient x y * (u * v) = mixedCoefficient x y * u * v
  ring

/-- Positive definiteness of the one-dimensional diagonal information pairing. -/
theorem mixedPairing_diagonal_pos (x u : ℝ) (hu : u ≠ 0) :
    0 < mixedPairing x x u u := by
  rw [mixedPairing_apply, mixedCoefficient_diagonal]
  have hsq : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  nlinarith

/-- The doubled metric is the generic canonical pullback of this mixed pairing. -/
def contrastNeutralMetric (x y : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  neutralPullback (mixedPairing x y)

@[simp] theorem contrastNeutralMetric_apply (x y : ℝ) (U V : ℝ × ℝ) :
    contrastNeutralMetric x y U V =
      mixedCoefficient x y * (U.1 * V.2 + V.1 * U.2) := by
  simp only [contrastNeutralMetric, neutralPullback_apply, mixedPairing_apply]
  ring

/-- Nondegeneracy of the actual pullback is exactly nonvanishing of its coefficient. -/
theorem contrastNeutralMetric_nondegenerate_iff (x y : ℝ) :
    (contrastNeutralMetric x y).Nondegenerate ↔ mixedCoefficient x y ≠ 0 := by
  rw [contrastNeutralMetric, neutralPullback_nondegenerate_iff]
  constructor
  · intro h hc
    have hz : (1 : ℝ) = 0 := h.1 1 (by
      intro v
      simp [hc])
    norm_num at hz
  · intro hc
    constructor
    · intro u hu
      have h : mixedCoefficient x y * u = 0 := by simpa using hu 1
      exact (mul_eq_zero.mp h).resolve_left hc
    · intro v hv
      have h : mixedCoefficient x y * v = 0 := by simpa using hv 1
      exact (mul_eq_zero.mp h).resolve_left hc

theorem contrastNeutralMetric_diagonal_nondegenerate (x : ℝ) :
    (contrastNeutralMetric x x).Nondegenerate := by
  rw [contrastNeutralMetric_nondegenerate_iff, mixedCoefficient_diagonal]
  norm_num

/-- An explicit nonzero vector in the radical at the off-diagonal point `(1,0)`. -/
theorem contrastNeutralMetric_one_zero_radical :
    ((1 : ℝ), (0 : ℝ)) ≠ (0 : ℝ × ℝ) ∧
      ∀ V : ℝ × ℝ, contrastNeutralMetric 1 0 (1, 0) V = 0 := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    norm_num at hfst
  · intro V
    simp

theorem contrastNeutralMetric_one_zero_degenerate :
    ¬(contrastNeutralMetric 1 0).Nondegenerate := by
  intro h
  exact contrastNeutralMetric_one_zero_radical.1
    (h.1 _ contrastNeutralMetric_one_zero_radical.2)

theorem not_forall_contrastNeutralMetric_nondegenerate :
    ¬∀ x y : ℝ, (contrastNeutralMetric x y).Nondegenerate := by
  intro h
  exact contrastNeutralMetric_one_zero_degenerate (h 1 0)

end InfoGeometry.InformationGeometry.ContrastMixedHessianBoundary
