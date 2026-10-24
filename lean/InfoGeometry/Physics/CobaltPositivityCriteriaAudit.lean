/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CobaltPositivityCriteria

open InfoGeometry.Physics.CobaltAsymmetry

example : ∀ θ, 0 ≤ gammaAngularModel 0 (-1) θ :=
  (gamma_nonneg_everywhere_iff 0 (-1)).2 (by norm_num)

example : ¬ ∀ θ, 0 ≤ gammaAngularModel 1 2 θ := by
  rw [gamma_nonneg_everywhere_iff]
  norm_num

example : ¬ ∀ θ, 0 ≤ betaAngularIntensity 2 θ := by
  rw [beta_nonneg_everywhere_iff]
  norm_num

example : ∀ θ, 0 ≤ betaAngularIntensity (-1) θ :=
  (beta_nonneg_everywhere_iff (-1)).2 (by norm_num)

#print axioms beta_nonneg_everywhere_iff
#print axioms gamma_nonneg_everywhere_iff
#print axioms anisotropy_does_not_imply_reflection_violation
