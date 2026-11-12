/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real classical cut density for `C³`

This is the explicit piecewise density in equations (3.5)--(3.7) of Cassia,
Longhi and Zabzine, *Symplectic Cuts and Open/Closed Strings I*.
For positive parameters its integral is the classical equivariant volume.
The density is continuous, with distinct one-sided derivatives at the wall.

The theorem concerns the displayed density. Identifying it with the pushforward
of a positive-orthant measure, or constructing the reduced symplectic manifold,
requires additional constructions not supplied by this module.
-/

noncomputable section

open MeasureTheory Set Real

namespace InfoGeometry.Analysis.SymplecticCutClassicalDensity

/-- The two real chambers of the classical cut density. -/
def classicalDensity (a b d c : ℝ) : ℝ :=
  if c ≤ 0 then exp (d * c) / (a * (b + d))
  else exp ((-b) * c) / (a * (b + d))

theorem classicalDensity_of_nonpos (a b d : ℝ) {c : ℝ} (hc : c ≤ 0) :
    classicalDensity a b d c = exp (d * c) / (a * (b + d)) := by
  simp only [classicalDensity, if_pos hc]

theorem classicalDensity_of_nonneg (a b d : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    classicalDensity a b d c = exp ((-b) * c) / (a * (b + d)) := by
  rcases eq_or_lt_of_le hc with h | h
  · subst c
    simp [classicalDensity]
  · simp only [classicalDensity, if_neg (not_le.mpr h)]

@[simp] theorem classicalDensity_zero (a b d : ℝ) :
    classicalDensity a b d 0 = 1 / (a * (b + d)) := by
  simp [classicalDensity]

theorem classicalDensity_pos {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (c : ℝ) : 0 < classicalDensity a b d c := by
  unfold classicalDensity
  split <;> exact div_pos (exp_pos _) (mul_pos ha (add_pos hb hd))

/-- The chamber formulas glue continuously at the wall, for all real parameters. -/
theorem continuous_classicalDensity (a b d : ℝ) :
    Continuous (classicalDensity a b d) := by
  change Continuous ((Iic (0 : ℝ)).piecewise
    (fun c => exp (d * c) / (a * (b + d)))
    (fun c => exp ((-b) * c) / (a * (b + d))))
  apply Continuous.piecewise
  · intro c hc
    have : c = 0 := by simpa only [frontier_Iic, mem_singleton_iff] using hc
    subst c
    simp
  · fun_prop
  · fun_prop

/-- Integrability follows from decay on the two half-lines. -/
theorem integrable_classicalDensity (a : ℝ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Integrable (classicalDensity a b d) := by
  change Integrable ((Iic (0 : ℝ)).piecewise
    (fun c => exp (d * c) / (a * (b + d)))
    (fun c => exp ((-b) * c) / (a * (b + d))))
  apply Integrable.piecewise measurableSet_Iic
  · exact (integrableOn_exp_mul_Iic hd 0).div_const _
  · simpa only [compl_Iic] using
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).div_const (a * (b + d))

/-- Integrating the cut level reconstructs the classical volume, equation (3.7). -/
theorem integral_classicalDensity {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) :
    (∫ c, classicalDensity a b d c) = 1 / (a * b * d) := by
  have hleft := (integrableOn_exp_mul_Iic hd 0).div_const (a * (b + d))
  have hright : IntegrableOn (fun c : ℝ => exp ((-b) * c) / (a * (b + d)))
      (Iic (0 : ℝ))ᶜ := by
    simpa only [compl_Iic] using
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).div_const (a * (b + d))
  change (∫ c, (Iic (0 : ℝ)).piecewise
    (fun c => exp (d * c) / (a * (b + d)))
    (fun c => exp ((-b) * c) / (a * (b + d))) c) = _
  rw [integral_piecewise measurableSet_Iic hleft hright, compl_Iic,
    integral_div, integral_div, integral_exp_mul_Iic hd,
    integral_exp_mul_Ioi (neg_neg_of_pos hb)]
  simp only [mul_zero, exp_zero]
  field_simp [ha.ne', hb.ne', hd.ne', (add_pos hb hd).ne']
  <;> ring

/-- The derivative from the negative chamber is positive for positive parameters. -/
theorem hasDerivWithinAt_classicalDensity_left (a b d : ℝ) :
    HasDerivWithinAt (classicalDensity a b d) (d / (a * (b + d))) (Iic 0) 0 := by
  have h : HasDerivAt (fun c : ℝ => exp (d * c) / (a * (b + d)))
      (d / (a * (b + d))) 0 := by
    simpa only [mul_zero, exp_zero, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).const_mul d).exp.div_const (a * (b + d)))
  exact h.hasDerivWithinAt.congr_of_mem
    (fun c hc => classicalDensity_of_nonpos a b d hc) (by simp)

/-- The derivative from the positive chamber is negative for positive parameters. -/
theorem hasDerivWithinAt_classicalDensity_right (a b d : ℝ) :
    HasDerivWithinAt (classicalDensity a b d) ((-b) / (a * (b + d))) (Ici 0) 0 := by
  have h : HasDerivAt (fun c : ℝ => exp ((-b) * c) / (a * (b + d)))
      ((-b) / (a * (b + d))) 0 := by
    simpa only [mul_zero, exp_zero, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (-b)).exp.div_const (a * (b + d)))
  exact h.hasDerivWithinAt.congr_of_mem
    (fun c hc => classicalDensity_of_nonneg a b d hc) (by simp)

/-- The classical wall is a genuine corner, unlike the smooth quantum density. -/
theorem not_differentiableAt_classicalDensity_zero {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ¬ DifferentiableAt ℝ (classicalDensity a b d) 0 := by
  intro h
  have hleft := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _
    (hasDerivWithinAt_classicalDensity_left a b d) h.hasDerivAt.hasDerivWithinAt
  have hright := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
    (hasDerivWithinAt_classicalDensity_right a b d) h.hasDerivAt.hasDerivWithinAt
  have hden : a * (b + d) ≠ 0 := (mul_pos ha (add_pos hb hd)).ne'
  have hbad : d = -b := (div_left_inj hden).mp (hleft.trans hright.symm)
  linarith

end InfoGeometry.Analysis.SymplecticCutClassicalDensity
