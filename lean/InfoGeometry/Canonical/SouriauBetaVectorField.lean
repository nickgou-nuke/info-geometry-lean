import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SouriauBetaVectorField

Finite constructive Souriau-`β` vector-field lane:

* `β` is modeled as a local flow generator,
* local temperature is constrained by an inverse-norm relation,
* a concrete Rindler-style profile gives the Unruh readout at `z = 1/a`.

This file is intentionally finite and theorem-safe (no Type III/KMS existence
claims).
-/

namespace InfoGeometry.Canonical.SouriauBetaVectorField

noncomputable section

/-- Minimal scalar Souriau field packet on a local 1D radial chart. -/
structure SouriauBetaScalar where
  beta : ℝ → ℝ
  localTemp : ℝ → ℝ
  temp_relation : ∀ z : ℝ, localTemp z = 1 / |beta z|

namespace SouriauBetaScalar

/-- Concrete wedge profile: `β(z) = 2π z` and `T(z) = 1 / |2π z|`. -/
def rindlerProfile : SouriauBetaScalar where
  beta := fun z => 2 * Real.pi * z
  localTemp := fun z => 1 / |2 * Real.pi * z|
  temp_relation := by intro z; rfl

@[simp] theorem rindlerProfile_beta (z : ℝ) :
    rindlerProfile.beta z = 2 * Real.pi * z := rfl

@[simp] theorem rindlerProfile_localTemp (z : ℝ) :
    rindlerProfile.localTemp z = 1 / |2 * Real.pi * z| := rfl

/--
Unruh-style horizon evaluation for the concrete profile:
if `a > 0` and `z = 1/a`, then `T(z) = a / (2π)`.
-/
theorem unruh_profile_at_horizon
    (a z : ℝ)
    (ha : 0 < a)
    (hz : z = 1 / a) :
    rindlerProfile.localTemp z = a / (2 * Real.pi) := by
  rw [hz, rindlerProfile_localTemp]
  have hpi : 0 < Real.pi := Real.pi_pos
  have htwoPi : 0 < 2 * Real.pi := by nlinarith
  have hInvA : 0 < 1 / a := by exact one_div_pos.mpr ha
  have hPos : 0 < 2 * Real.pi * (1 / a) := by nlinarith
  rw [abs_of_pos hPos]
  field_simp [ha.ne']

/--
The concrete profile exactly satisfies the inverse-temperature law by
construction.
-/
theorem rindlerProfile_temp_relation_exact (z : ℝ) :
    rindlerProfile.localTemp z = 1 / |rindlerProfile.beta z| := by
  simpa [rindlerProfile_beta] using rindlerProfile.temp_relation z

end SouriauBetaScalar

end

end InfoGeometry.Canonical.SouriauBetaVectorField
