/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Modular.PSL2Z
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# The finite modular action interface

This file adds the first analytic fact needed by the modular action corridor:
an integral determinant-one matrix has no Möbius denominator zero in the upper
half-plane.  The quotient action and any U-duality interpretation remain
separate future layers.
-/

namespace InfoGeometry.Modular.PSL2Z

open Complex

def upperHalfPlane (z : ℂ) : Prop := 0 < z.im

noncomputable def mobiusAction (A : SL2Z) (z : ℂ) : ℂ :=
  (((A.val 0 0 : ℂ) * z + (A.val 0 1 : ℂ)) /
    ((A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ)))

theorem mobius_denominator_ne_zero {A : SL2Z} {z : ℂ}
    (hz : upperHalfPlane z) :
    (A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ) ≠ 0 := by
  intro hden
  have him : (A.val 1 0 : ℝ) * z.im = 0 := by
    have him' := congrArg Complex.im hden
    simpa [Complex.add_im, Complex.mul_im] using him'
  by_cases hc : A.val 1 0 = 0
  · have hd : A.val 1 1 = 0 := by
      have hre := congrArg Complex.re hden
      simpa [hc] using hre
    have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := A.property
    rw [hc, hd] at hdet
    norm_num at hdet
  · have hcR : (A.val 1 0 : ℝ) ≠ 0 := by
      exact_mod_cast hc
    have : (A.val 1 0 : ℝ) * z.im ≠ 0 :=
      mul_ne_zero hcR (ne_of_gt hz)
    exact this him

theorem mobiusAction_im_formula {A : SL2Z} {z : ℂ} :
    (mobiusAction A z).im =
      z.im / Complex.normSq ((A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ)) := by
  have hdet :
      (A.val 0 0 : ℝ) * (A.val 1 1 : ℝ) -
          (A.val 0 1 : ℝ) * (A.val 1 0 : ℝ) = 1 := by
    exact_mod_cast A.property
  unfold mobiusAction
  rw [Complex.div_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  linear_combination z.im * (Complex.normSq ((A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ)))⁻¹ * hdet

theorem mobiusAction_maps_upperHalfPlane {A : SL2Z} {z : ℂ}
    (hz : upperHalfPlane z) : upperHalfPlane (mobiusAction A z) := by
  unfold upperHalfPlane
  rw [mobiusAction_im_formula]
  have hden : 0 < Complex.normSq ((A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ)) :=
    Complex.normSq_pos.mpr (mobius_denominator_ne_zero hz)
  exact div_pos hz hden

end InfoGeometry.Modular.PSL2Z
