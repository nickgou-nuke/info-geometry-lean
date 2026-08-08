import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Convex.SelfConcordantLogBarrier

Native theorem: the standard logarithmic barrier on the positive real line
satisfies the one-dimensional self-concordance curvature inequality.

This file proves the finite algebraic curvature identity

  `|F'''(x)| = 2 * (F''(x))^(3/2)`

for the standard barrier `F(x) = -log x`, represented by its explicit curvature
readouts

  `F''(x) = x⁻¹ ^ 2`,
  `|F'''(x)| = 2 * x⁻¹ ^ 3`,

on `x > 0`.

No zeta theorem.
No analytic continuation.
No RH claim.
No socket.
No property.
-/

noncomputable section

namespace InfoGeometry.Convex.SelfConcordantLogBarrier

/-- The standard logarithmic barrier on the positive real line. -/
@[rep_depth thermo]
def logBarrier (x : ℝ) : ℝ :=
  - Real.log x

/-- Explicit Hessian readout for `F(x) = -log x`: `F''(x) = x⁻²`. -/
@[rep_depth thermo]
def logBarrierHessian (x : ℝ) : ℝ :=
  x⁻¹ ^ 2

/-- Explicit absolute third-derivative readout: `|F'''(x)| = 2x⁻³`. -/
@[rep_depth thermo]
def logBarrierThirdAbs (x : ℝ) : ℝ :=
  2 * x⁻¹ ^ 3

/--
One-dimensional self-concordance curvature predicate.

This is the pointwise Nesterov--Nemirovski inequality

`thirdAbs x ≤ 2 * (sqrt (hess x))^3`.
-/
@[rep_depth thermo]
def OneDimSelfConcordantCurvature
    (hess thirdAbs : ℝ → ℝ)
    (Ω : Set ℝ) : Prop :=
  ∀ x, x ∈ Ω → thirdAbs x ≤ 2 * (Real.sqrt (hess x)) ^ 3

/-- On `x > 0`, the Hessian readout is strictly positive. -/
@[rep_depth thermo]
theorem logBarrierHessian_pos
    {x : ℝ}
    (hx : 0 < x) :
    0 < logBarrierHessian x := by
  unfold logBarrierHessian
  positivity

/-- On `x > 0`, the Hessian readout is nonnegative. -/
@[rep_depth thermo]
theorem logBarrierHessian_nonneg
    {x : ℝ}
    (hx : 0 < x) :
    0 ≤ logBarrierHessian x := by
  exact le_of_lt (logBarrierHessian_pos hx)

/--
The square-root of the Hessian readout is `x⁻¹` on the positive real line.
-/
@[rep_depth thermo]
theorem sqrt_logBarrierHessian
    {x : ℝ}
    (hx : 0 < x) :
    Real.sqrt (logBarrierHessian x) = x⁻¹ := by
  unfold logBarrierHessian
  have hnonneg : 0 ≤ x⁻¹ := by
    exact le_of_lt (inv_pos.mpr hx)
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg hnonneg

/--
Exact one-dimensional self-concordance equality for the logarithmic barrier.

`|F'''(x)| = 2 * (sqrt (F''(x)))^3`.
-/
@[rep_depth thermo]
theorem logBarrier_selfConcordant_exact
    {x : ℝ}
    (hx : 0 < x) :
    logBarrierThirdAbs x =
      2 * (Real.sqrt (logBarrierHessian x)) ^ 3 := by
  rw [sqrt_logBarrierHessian hx]
  rfl

/--
The standard logarithmic barrier satisfies the self-concordance inequality
on the positive real line.
-/
@[rep_depth thermo]
theorem logBarrier_selfConcordant_core
    {x : ℝ}
    (hx : 0 < x) :
    logBarrierThirdAbs x ≤
      2 * (Real.sqrt (logBarrierHessian x)) ^ 3 := by
  rw [logBarrier_selfConcordant_exact hx]

/--
The standard logarithmic barrier is self-concordant on `Set.Ioi 0`
in the explicit one-dimensional curvature sense.
-/
@[rep_depth thermo]
theorem logBarrier_selfConcordant_on_Ioi :
    OneDimSelfConcordantCurvature
      logBarrierHessian
      logBarrierThirdAbs
      (Set.Ioi (0 : ℝ)) := by
  intro x hx
  exact logBarrier_selfConcordant_core hx

/--
The native self-concordant logarithmic barrier owner target is closed.

This is deliberately only the standard positive-line log barrier.  It is not
a theorem about `-log ζ`.
-/
theorem selfConcordantLogBarrierOwnerTarget :
    OneDimSelfConcordantCurvature
      logBarrierHessian
      logBarrierThirdAbs
      (Set.Ioi (0 : ℝ)) :=
  logBarrier_selfConcordant_on_Ioi

@[owner_target_tag, rep_depth thermo]
theorem selfConcordantLogBarrier_packet :
    (∀ x, x ∈ Set.Ioi (0 : ℝ) →
      logBarrierThirdAbs x ≤ 2 * (Real.sqrt (logBarrierHessian x)) ^ 3) ∧
      (∀ {x : ℝ}, 0 < x →
        logBarrierThirdAbs x = 2 * (Real.sqrt (logBarrierHessian x)) ^ 3) := by
  exact ⟨selfConcordantLogBarrierOwnerTarget, fun hx => logBarrier_selfConcordant_exact hx⟩

end InfoGeometry.Convex.SelfConcordantLogBarrier
