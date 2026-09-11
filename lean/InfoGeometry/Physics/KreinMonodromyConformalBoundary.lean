import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

/-! Algebraic scaling readouts on a bilinear carrier.  No Krein-space
structure is introduced here: positivity, nondegeneracy, and an involution are
separate hypotheses when a concrete model needs them. -/

noncomputable def logDerivForm (Q dQ : ℝ) : ℝ :=
  dQ / Q

def kreinProbability
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (bilin : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (eta : V →ₗ[ℝ] V) (psi : V) : ℝ :=
  bilin psi (eta psi)

theorem krein_amplitude_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (bilin : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (eta : V →ₗ[ℝ] V) (psi : V) (c : ℝ) :
    kreinProbability bilin eta (c • psi) =
      c * c * kreinProbability bilin eta psi := by
  simp only [kreinProbability, LinearMap.map_smul, LinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

theorem probability_to_amplitude_born_recovery (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt p * Real.sqrt p = p :=
  Real.mul_self_sqrt hp

end InfoGeometry.Physics
