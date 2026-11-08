import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.HestenesLoxodromicRotor

namespace InfoGeometry.Canonical.UnruhLoxodromicPackaging

noncomputable section

/-!
This owner packages the real thermodynamic rapidity already used by the
repository with the independent circular rotor parameter.  No complex scalar,
analytic continuation, or spectral existence assertion is introduced here.
-/

def unruhInverseTemperature (a : ℝ) : ℝ := 2 * Real.pi / a

def chiralRapidity (a μχ : ℝ) : ℝ :=
  unruhInverseTemperature a * μχ

def loxodromicParameters (a μχ θ : ℝ) : ℝ × ℝ :=
  (chiralRapidity a μχ, θ)

@[simp] theorem unruhInverseTemperature_def (a : ℝ) :
    unruhInverseTemperature a = 2 * Real.pi / a := rfl

@[simp] theorem chiralRapidity_def (a μχ : ℝ) :
    chiralRapidity a μχ = (2 * Real.pi / a) * μχ := rfl

theorem loxodromicParameters_fst (a μχ θ : ℝ) :
    (loxodromicParameters a μχ θ).1 = (2 * Real.pi / a) * μχ := by
  rfl

theorem loxodromicParameters_snd (a μχ θ : ℝ) :
    (loxodromicParameters a μχ θ).2 = θ := by
  rfl

theorem chiralRapidity_eq_unruh_inverse_mul (a μχ : ℝ) :
    chiralRapidity a μχ = unruhInverseTemperature a * μχ := rfl

theorem chiralRapidity_zero_of_zero_chemical_potential (a : ℝ) :
    chiralRapidity a 0 = 0 := by
  simp [chiralRapidity]

theorem chiralRapidity_eq_zero_of_nonzero_acceleration
    {a μχ : ℝ} (ha : a ≠ 0) :
    chiralRapidity a μχ = 0 ↔ μχ = 0 := by
  unfold chiralRapidity unruhInverseTemperature
  constructor
  · intro h
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [ha] at h
    simp only [mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hπ
  · intro h
    rw [h, mul_zero]

theorem loxodromicParameters_eq
    (a μχ θ : ℝ) :
    loxodromicParameters a μχ θ = ((2 * Real.pi / a) * μχ, θ) := by
  rfl

end

end InfoGeometry.Canonical.UnruhLoxodromicPackaging
