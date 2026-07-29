/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GibbsFluctuation

/-!
# Finite Gibbs scalar stability

This module states the exact finite scalar resolvability boundary. It is a
local curvature result, not a claim of global optimization or a thermodynamic
limit.
-/

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

theorem scalar_instability
    (w h₂ f : Data → ℝ) (ε : ℝ)
    (h_unstable : fluctuationPressure w f ε ≥ fisherStiffness w h₂) :
    ¬ 0 < exactScalarHessian w h₂ f ε := by
  intro h_pos
  unfold exactScalarHessian at h_pos
  linarith

theorem scalar_stability_implies_stiffness_gt_fluctuation
    (w h₂ f : Data → ℝ) (ε : ℝ)
    (h_stable : 0 < exactScalarHessian w h₂ f ε) :
    fluctuationPressure w f ε < fisherStiffness w h₂ := by
  unfold exactScalarHessian at h_stable
  linarith

/--
The exact scalar Hessian is stiffness minus the temperature-scaled pairwise
disagreement energy.  This is the explicit finite stability form used by the
thermodynamic regression diagnostics.
-/
theorem exactScalarHessian_eq_stiffness_sub_pairwise
    (w h₂ f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∑ i : Data, w i = 1) :
    exactScalarHessian w h₂ f ε =
      fisherStiffness w h₂ -
        (1 / (2 * ε) : ℝ) * ∑ i : Data, ∑ j : Data,
          w i * w j * (f i - f j) ^ 2 := by
  unfold exactScalarHessian
  rw [fluctuationPressure_eq_half_pairwise w f ε hε hw]

/--
At positive temperature, strict scalar resolvability is equivalent to the
pairwise disagreement pressure remaining below Fisher stiffness.
-/
theorem exactScalarHessian_pos_iff_pairwise
    (w h₂ f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∑ i : Data, w i = 1) :
    0 < exactScalarHessian w h₂ f ε ↔
      (1 / (2 * ε) : ℝ) * ∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2 < fisherStiffness w h₂ := by
  rw [exactScalarHessian_eq_stiffness_sub_pairwise w h₂ f ε hε hw]
  exact sub_pos

end InfoGeometry.Inference
