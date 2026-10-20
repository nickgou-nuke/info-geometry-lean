/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/


import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry


/-!
# Thermal commutator–anticommutator balance

This file derives the hyperbolic balance coefficient directly from the
repository's native Fermi occupation and occupation-odds definitions.
No operator identity or KMS theorem is inferred from this scalar readout.
-/

namespace InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

/-- The thermal commutator/anticommutator balance coefficient is the
hyperbolic tangent of half the mode energy. -/
theorem occupationOdds_balance_coefficient (β ξ : ℝ) :
    (1 - occupationOdds β ξ) / (1 + occupationOdds β ξ) =
      Real.tanh (β * ξ / 2) := by
  rw [occupationOdds_eq_exp_neg]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h₁ : Real.exp (β * ξ / 2) ≠ 0 := Real.exp_ne_zero _
  have h₂ : Real.exp (-(β * ξ / 2)) ≠ 0 := Real.exp_ne_zero _
  have hsum : Real.exp (-(β * ξ / 2)) + Real.exp (β * ξ / 2) ≠ 0 := by
    positivity
  field_simp [h₁, h₂, hsum]
  have hsq : Real.exp (-(β * ξ)) =
      Real.exp (-(β * ξ / 2)) * Real.exp (-(β * ξ / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (β * ξ / 2) * Real.exp (-(β * ξ / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hsq]
  apply sub_eq_zero.mp
  calc
    (1 - Real.exp (-(β * ξ / 2)) * Real.exp (-(β * ξ / 2))) *
          (Real.exp (β * ξ / 2) + Real.exp (-(β * ξ / 2))) -
        (1 + Real.exp (-(β * ξ / 2)) * Real.exp (-(β * ξ / 2))) *
          (Real.exp (β * ξ / 2) - Real.exp (-(β * ξ / 2))) =
      2 * Real.exp (-(β * ξ / 2)) *
        (1 - Real.exp (β * ξ / 2) * Real.exp (-(β * ξ / 2))) := by ring
    _ = 0 := by rw [hprod]; ring

end InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
