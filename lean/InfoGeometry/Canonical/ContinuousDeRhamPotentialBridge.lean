import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore

/-!
# Logarithmic potentials along real parameterized functions

For `trajectoryPotential γ γ₀ t = -log (γ t) + log γ₀`, this owner
proves a derivative formula at positive differentiability points, unconditional
endpoint-difference identities, and an interval integral formula under explicit
positivity, differentiability, and integrability hypotheses.

Endpoint equality alone gives a zero potential difference. Its interpretation
as a zero integral additionally requires the hypotheses of
`integral_logarithmicDerivative`. No cohomology identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ContinuousDeRhamPotentialBridge

/-- The scalar potential along a parameterized positive density trajectory γ(t) with reference density γ₀. -/
def trajectoryPotential (γ : ℝ → ℝ) (γ₀ : ℝ) (t : ℝ) : ℝ :=
  -Real.log (γ t) + Real.log γ₀

/-- 
  THEOREM 1: Derivative of the 0-Form Potential (The Exact 1-Form Maurer-Cartan Velocity).
  If γ has derivative γ'(t) at t and γ(t) > 0, then:
    d/dt [ -ln γ(t) + ln γ₀ ] = - (γ'(t) / γ(t))
-/
theorem hasDerivAt_trajectoryPotential
    {γ : ℝ → ℝ} {γ' : ℝ} {γ₀ : ℝ} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (hpos : 0 < γ t) :
    HasDerivAt (fun s => trajectoryPotential γ γ₀ s) (- (γ' / γ t)) t := by
  dsimp [trajectoryPotential]
  have h_log_deriv : HasDerivAt (fun s => Real.log (γ s)) ((γ t)⁻¹ * γ') t :=
    (Real.hasDerivAt_log hpos.ne').comp t hγ
  have h_eq : (γ t)⁻¹ * γ' = γ' / γ t := by
    rw [mul_comm, div_eq_mul_inv]
  rw [h_eq] at h_log_deriv
  have h_neg_log : HasDerivAt (fun s => -Real.log (γ s)) (- (γ' / γ t)) t :=
    HasDerivAt.neg h_log_deriv
  have h_const : HasDerivAt (fun _ : ℝ => Real.log γ₀) 0 t := hasDerivAt_const t (Real.log γ₀)
  have h_add := HasDerivAt.add h_neg_log h_const
  rw [add_zero] at h_add
  exact h_add

/-- 
  THEOREM 2: The Continuous Maurer-Cartan 1-Form Evaluation.
  The derivative of the potential is identically the negative logarithmic derivative:
    deriv (trajectoryPotential γ γ₀) t = - (γ'(t) / γ(t))
-/
theorem deriv_trajectoryPotential
    {γ : ℝ → ℝ} {γ' : ℝ} {γ₀ : ℝ} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (hpos : 0 < γ t) :
    deriv (trajectoryPotential γ γ₀) t = - (γ' / γ t) :=
  (hasDerivAt_trajectoryPotential hγ hpos).deriv

/-- The reference constant cancels in the endpoint difference. -/
theorem trajectoryPotential_difference
    (γ : ℝ → ℝ) (γ₀ : ℝ) (t₀ t₁ : ℝ) :
    trajectoryPotential γ γ₀ t₁ - trajectoryPotential γ γ₀ t₀ =
      -Real.log (γ t₁) + Real.log (γ t₀) := by
  dsimp [trajectoryPotential]
  ring

/-- Equal endpoint values give zero potential difference. -/
theorem trajectoryPotential_closed_loop
    (γ : ℝ → ℝ) (γ₀ : ℝ) (t₀ t₁ : ℝ) (h_loop : γ t₁ = γ t₀) :
    trajectoryPotential γ γ₀ t₁ - trajectoryPotential γ γ₀ t₀ = 0 := by
  rw [trajectoryPotential_difference]
  rw [h_loop]
  ring

/-- The negative logarithmic derivative integrates to the logarithmic
endpoint difference on an interval where the function is positive. -/
theorem integral_logarithmicDerivative
    {γ γ' : ℝ → ℝ} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t)
    (hi : IntervalIntegrable (fun t => -(γ' t / γ t))
      MeasureTheory.volume a b) :
    (∫ t in a..b, -(γ' t / γ t)) = -Real.log (γ b) + Real.log (γ a) := by
  calc
    (∫ t in a..b, -(γ' t / γ t)) =
        trajectoryPotential γ 1 b - trajectoryPotential γ 1 a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
      intro t ht
      exact hasDerivAt_trajectoryPotential (hγ t ht) (hpos t ht)
    _ = -Real.log (γ b) + Real.log (γ a) :=
      trajectoryPotential_difference γ 1 a b

end InfoGeometry.Canonical.ContinuousDeRhamPotentialBridge

end noncomputable section
