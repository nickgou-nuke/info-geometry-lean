import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-!
# Global Lyapunov theorem for the self-concordant log-generating potential

The bare logarithmic barrier `-log x` is self-concordant on `x > 0`, but it has
no interior minimum.  The normalized log-generating/Bregman potential

  V(x) = x - log x - 1

has the same Hessian and third derivative and therefore the same
self-concordant geometry, while possessing the unique minimum `x = 1`.

For the Hessian/Fisher metric

  g(x) = V''(x) = 1/x^2,

the negative natural-gradient vector field with mobility `kappa >= 0` is

  X_kappa(x) = -kappa * g(x)^{-1} * V'(x)
             = -kappa * x * (x - 1).

The Lie derivative of `V` along this field is the exact global identity

  L_X V = -kappa * (x - 1)^2.

Hence `V` is nonincreasing on the whole positive domain, and for `kappa > 0`
it is strictly decreasing away from its unique minimizer/equilibrium `x = 1`.
This is a state-space Lyapunov theorem.  It does not assume or assert any
Riemann-hypothesis statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

open Real
open InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-- The normalized log-generating potential. -/
abbrev lyapunovPotential : ℝ → ℝ := isBarrierKernel

/-- Its genuine first derivative. -/
theorem hasDerivAt_lyapunovPotential {x : ℝ} (hx : 0 < x) :
    HasDerivAt lyapunovPotential (1 - 1 / x) x := by
  change HasDerivAt (fun y : ℝ => y - Real.log y - 1) (1 - 1 / x) x
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  convert ((hasDerivAt_id x).sub hlog).sub_const 1 using 1 <;> ring

/-- The Hessian/Fisher metric coefficient `g = V'' = 1/x^2`. -/
def fisherMetric (x : ℝ) : ℝ := 1 / x ^ 2

/-- The inverse Hessian/Fisher metric coefficient. -/
def inverseFisherMetric (x : ℝ) : ℝ := x ^ 2

/-- The negative natural-gradient field of `V` with mobility `kappa`. -/
def naturalGradientField (kappa x : ℝ) : ℝ :=
  -kappa * x * (x - 1)

/-- The natural-gradient definition agrees with `-kappa g^{-1} V'`. -/
theorem naturalGradientField_eq_metric_gradient
    (kappa x : ℝ) (hx : 0 < x) :
    naturalGradientField kappa x =
      -kappa * inverseFisherMetric x * isBarrierKernel_deriv x := by
  unfold naturalGradientField inverseFisherMetric isBarrierKernel_deriv
  field_simp [ne_of_gt hx]
  ring

/-- Pointwise Lie derivative of the Lyapunov potential along the field. -/
def lyapunovLieDerivative (kappa x : ℝ) : ℝ :=
  isBarrierKernel_deriv x * naturalGradientField kappa x

/-- Exact global dissipation identity. -/
theorem lyapunovLieDerivative_eq
    (kappa x : ℝ) (hx : 0 < x) :
    lyapunovLieDerivative kappa x = -kappa * (x - 1) ^ 2 := by
  unfold lyapunovLieDerivative naturalGradientField isBarrierKernel_deriv
  field_simp [ne_of_gt hx]
  ring

/-- For nonnegative mobility the potential is nonincreasing everywhere. -/
theorem lyapunovLieDerivative_nonpos
    {kappa x : ℝ} (hkappa : 0 ≤ kappa) (hx : 0 < x) :
    lyapunovLieDerivative kappa x ≤ 0 := by
  rw [lyapunovLieDerivative_eq kappa x hx]
  exact neg_nonpos.mpr (mul_nonneg hkappa (sq_nonneg (x - 1)))

/-- For positive mobility the Lyapunov decrease is strict away from the valley. -/
theorem lyapunovLieDerivative_neg
    {kappa x : ℝ} (hkappa : 0 < kappa) (hx : 0 < x) (hx1 : x ≠ 1) :
    lyapunovLieDerivative kappa x < 0 := by
  rw [lyapunovLieDerivative_eq kappa x hx]
  have hs : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx1)
  exact neg_neg_of_pos (mul_pos hkappa hs)

/-- The potential is globally nonnegative on the positive domain. -/
theorem lyapunovPotential_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤ lyapunovPotential x :=
  isBarrierKernel_nonneg x hx

/-- The information-geometric valley is the unique zero/minimum `x = 1`. -/
theorem lyapunovPotential_eq_zero_iff
    {x : ℝ} (hx : 0 < x) :
    lyapunovPotential x = 0 ↔ x = 1 :=
  isBarrierKernel_eq_zero_iff x hx

/-- Strict positivity away from the information-geometric valley. -/
theorem lyapunovPotential_pos
    {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    0 < lyapunovPotential x :=
  isBarrierKernel_pos x hx hx1

/-- The natural-gradient field has exactly one equilibrium on the positive domain. -/
theorem naturalGradientField_eq_zero_iff
    {kappa x : ℝ} (hkappa : 0 < kappa) (hx : 0 < x) :
    naturalGradientField kappa x = 0 ↔ x = 1 := by
  unfold naturalGradientField
  constructor
  · intro h
    have hk : kappa ≠ 0 := ne_of_gt hkappa
    have hx0 : x ≠ 0 := ne_of_gt hx
    rcases mul_eq_zero.mp h with h1 | h1
    · exact False.elim (hk (neg_eq_zero.mp h1))
    · rcases mul_eq_zero.mp h1 with hxz | hxm
      · exact False.elim (hx0 hxz)
      · exact sub_eq_zero.mp hxm
  · intro h
    subst x
    ring

/-- Below the valley the natural-gradient field points upward. -/
theorem naturalGradientField_pos_below
    {kappa x : ℝ} (hkappa : 0 < kappa) (hx : 0 < x) (hx1 : x < 1) :
    0 < naturalGradientField kappa x := by
  unfold naturalGradientField
  have hxm : x - 1 < 0 := sub_neg.mpr hx1
  nlinarith [mul_pos hkappa hx]

/-- Above the valley the natural-gradient field points downward. -/
theorem naturalGradientField_neg_above
    {kappa x : ℝ} (hkappa : 0 < kappa) (hx1 : 1 < x) :
    naturalGradientField kappa x < 0 := by
  unfold naturalGradientField
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hxm : 0 < x - 1 := sub_pos.mpr hx1
  nlinarith [mul_pos hkappa hx, mul_pos hx hxm]

/-- The normalized log-generating potential inherits the exact self-concordance identity. -/
theorem lyapunovPotential_selfConcordance
    {x : ℝ} (hx : 0 < x) :
    |isBarrierKernel_deriv3 x| =
      2 * isBarrierKernel_deriv2 x ^ (3 / 2 : ℝ) :=
  isBarrierKernel_selfConcordance x hx

/--
Global strict Lyapunov theorem on the full positive state space.

For every `x > 0` and every positive mobility:
* `V(x) >= 0`;
* `V(x)=0` iff `x=1`;
* the Hessian is positive;
* self-concordance holds;
* `L_X V = -kappa (x-1)^2 <= 0`;
* equality of the vector field with zero occurs iff `x=1`;
* away from `x=1`, `L_X V < 0`.
-/
theorem global_selfConcordant_lyapunov
    (kappa x : ℝ) (hkappa : 0 < kappa) (hx : 0 < x) :
    (0 ≤ lyapunovPotential x) ∧
    (lyapunovPotential x = 0 ↔ x = 1) ∧
    (0 < isBarrierKernel_deriv2 x) ∧
    (|isBarrierKernel_deriv3 x| =
      2 * isBarrierKernel_deriv2 x ^ (3 / 2 : ℝ)) ∧
    (lyapunovLieDerivative kappa x = -kappa * (x - 1) ^ 2) ∧
    (lyapunovLieDerivative kappa x ≤ 0) ∧
    (naturalGradientField kappa x = 0 ↔ x = 1) ∧
    (x ≠ 1 → lyapunovLieDerivative kappa x < 0) := by
  refine ⟨lyapunovPotential_nonneg hx,
    lyapunovPotential_eq_zero_iff hx,
    isBarrierKernel_deriv2_pos x hx,
    lyapunovPotential_selfConcordance hx,
    lyapunovLieDerivative_eq kappa x hx,
    lyapunovLieDerivative_nonpos (le_of_lt hkappa) hx,
    naturalGradientField_eq_zero_iff hkappa hx,
    ?_⟩
  intro hx1
  exact lyapunovLieDerivative_neg hkappa hx hx1

end InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

end noncomputable section
