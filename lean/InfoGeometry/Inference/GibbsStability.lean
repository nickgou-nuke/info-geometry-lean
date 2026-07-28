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

end InfoGeometry.Inference
