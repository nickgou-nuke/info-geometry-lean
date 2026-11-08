/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CobaltAsymmetry

/-! Exact positivity domains for the existing angular models.
These statements concern the defined real functions, not a physical inference
from anisotropy to reflection symmetry violation. -/
namespace InfoGeometry.Physics.CobaltAsymmetry

theorem beta_nonneg_everywhere_iff (a : ℝ) :
    (∀ θ, 0 ≤ betaAngularIntensity a θ) ↔ |a| ≤ 1 := by
  constructor
  · intro h
    have h₀ := h 0
    have hπ := h Real.pi
    simp only [betaAngularIntensity, Real.cos_zero, mul_one] at h₀
    simp only [betaAngularIntensity, Real.cos_pi, mul_neg_one, sub_neg_eq_add] at hπ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro h θ
    exact betaAngularIntensity_nonneg a θ h

theorem gamma_nonneg_everywhere_iff (a k : ℝ) :
    (∀ θ, 0 ≤ gammaAngularModel a k θ) ↔ k ≤ a ^ 2 := by
  constructor
  · intro h
    have he := h (Real.pi / 2)
    rw [gamma_equator_value] at he
    exact sub_nonneg.mp he
  · intro h θ
    by_cases hk : 0 ≤ k
    · exact gamma_nonneg a k θ hk h
    · have hm : k * (Real.sin θ) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) (sq_nonneg _)
      unfold gammaAngularModel
      exact sub_nonneg.mpr (hm.trans (sq_nonneg a))

end InfoGeometry.Physics.CobaltAsymmetry
