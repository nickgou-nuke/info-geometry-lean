import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite angles of the native `KRotation` flow

These lemmas isolate the finite subgroup already present in the continuous
phase flow.  They do not identify the abstract carrier with a particular
`Cl(1,1)` matrix slice; that requires a separate representation theorem.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.BogoliubovClosedForms

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem KRotation_pi_div_two (u : DoubledSpace E) :
    KRotation (Real.pi / 2) u = clockAxis (E := E) u := by
  rw [KRotation_apply]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem KRotation_pi (u : DoubledSpace E) :
    KRotation Real.pi u = -u := by
  rw [KRotation_apply]
  rw [Real.cos_pi, Real.sin_pi]
  simp

theorem KRotation_three_pi_div_two (u : DoubledSpace E) :
    KRotation (3 * Real.pi / 2) u = -clockAxis (E := E) u := by
  rw [KRotation_apply]
  have hangle : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [hangle, Real.cos_add, Real.sin_add]
  rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

end InfoGeometry.Canonical.BogoliubovClosedForms
