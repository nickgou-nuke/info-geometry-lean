import Mathlib

/-!
# InfoGeometry.Canonical.SouriauBetaField

Finite Souriau beta-field seed for the modular/thermodynamic corridor.

This file is intentionally local and witness-driven:

* no global AQFT theorem is asserted,
* no Type III modular completion is asserted,
* only explicit finite identities are proved.
-/

namespace SouriauBetaField

structure SouriauVectorField where
  beta : ℝ → ℝ
  /-- Local temperature readout driven by the beta norm. -/
  localTemp : ℝ → ℝ
  /-- Tolman-style local relation in the 1D seed. -/
  temp_relation : ∀ x : ℝ, localTemp x = 1 / |beta x|

/-- Antisymmetric bilinear seed modeling a 1D Killing-style cancellation law. -/
def killForm (S : SouriauVectorField) (x v w : ℝ) : Prop :=
  S.beta x * v + v * S.beta w = 0

/-- Symmetric point specialization of the killing seed. -/
theorem killForm_self (S : SouriauVectorField) (x v : ℝ)
    (h : S.beta x = 0) :
    killForm S x v x := by
  unfold killForm
  simp [h]

/--
Unruh-profile readout at the horizon in the finite scalar seed:
if `z = 1 / a` and the beta norm witness is `|β(z)| = 2π/a`,
then `T(z) = a / (2π)`.
-/
theorem unruh_profile_at_horizon
    (S : SouriauVectorField) (a z : ℝ)
    (ha : 0 < a)
    (hz : z = 1 / a)
    (hbeta : |S.beta z| = 2 * Real.pi / a) :
    S.localTemp z = a / (2 * Real.pi) := by
  have _ := hz
  have htemp : S.localTemp z = 1 / |S.beta z| := S.temp_relation z
  rw [htemp, hbeta]
  field_simp [ha.ne', Real.pi_ne_zero]

end SouriauBetaField
