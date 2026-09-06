import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Finite-time invariance for an exponential linear flow

This is the analytic part of the trace-preservation statement.  It assumes
only a complete real normed state space and a continuous linear trace
functional; no positivity or semigroup contractivity is smuggled into the
definition.
-/

noncomputable section

namespace InfoGeometry.Modular.SchrodingerFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "EndE" => E →L[ℝ] E

noncomputable local instance : NormedRing EndE := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndE := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndE :=
  NormedAlgebra.restrictScalars ℚ ℝ EndE

noncomputable def flow (L : EndE) (t : ℝ) : EndE :=
  NormedSpace.exp (t • L)

@[simp] theorem flow_zero (L : EndE) : flow L 0 = 1 := by
  simp [flow]

variable [CompleteSpace E]

theorem flow_add (L : EndE) (s t : ℝ) :
    flow L (s + t) = flow L s * flow L t := by
  simpa [flow, add_smul] using
    (NormedSpace.exp_add_of_commute
      (((Commute.refl L).smul_left s).smul_right t))

theorem hasStrictDerivAt_flow_left (L : EndE) (t : ℝ) :
    HasStrictDerivAt (flow L) (L * flow L t) t := by
  simpa [flow] using (hasStrictDerivAt_exp_smul_const' L t)

private noncomputable def evalState : EndE →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.apply ℝ E).flip

theorem hasDerivAt_orbit (L : EndE) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow L s x) (L (flow L t x)) t := by
  have h := (evalState (E := E)).hasStrictDerivAt_of_bilinear
    (hasStrictDerivAt_flow_left L t) (hasStrictDerivAt_const t x)
  simpa [evalState, ContinuousLinearMap.comp_apply] using h |>.hasDerivAt

theorem trace_flow_preservation
    (L : EndE) (τ : E →L[ℝ] ℝ)
    (hL : ∀ x : E, τ (L x) = 0) (x : E) (t : ℝ) :
    τ (flow L t x) = τ x := by
  let f : ℝ → ℝ := fun s => τ (flow L s x)
  have hderiv : ∀ s : ℝ, HasDerivAt f 0 s := by
    intro s
    have h := τ.hasFDerivAt.comp s
      (hasDerivAt_orbit L x s).hasFDerivAt
    have hd := h.hasDerivAt
    simpa [f, hL] using hd
  have hdiff : Differentiable ℝ f := fun s => (hderiv s).differentiableAt
  have hz : ∀ s : ℝ, deriv f s = 0 := fun s => (hderiv s).deriv
  have hc := is_const_of_deriv_eq_zero hdiff hz t 0
  dsimp [f] at hc
  simpa [flow_zero] using hc

end InfoGeometry.Modular.SchrodingerFlow

end noncomputable section
