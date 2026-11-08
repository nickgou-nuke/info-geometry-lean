/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GibbsFluctuation
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/--
When Fisher stiffness is positive, scalar stability is equivalent to the
temperature exceeding the explicit pairwise-disagreement threshold
`D / (2 A)`, where `D` is the finite pairwise energy and `A` is stiffness.
-/
theorem exactScalarHessian_pos_iff_temperature_gt_critical
    (w h₂ f : Data → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hw : ∑ i : Data, w i = 1)
    (hA : 0 < fisherStiffness w h₂) :
    0 < exactScalarHessian w h₂ f ε ↔
      (∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2) / (2 * fisherStiffness w h₂) < ε := by
  rw [exactScalarHessian_pos_iff_pairwise w h₂ f ε hε hw]
  let D : ℝ := ∑ i : Data, ∑ j : Data,
    w i * w j * (f i - f j) ^ 2
  let A : ℝ := fisherStiffness w h₂
  change (1 / (2 * ε)) * D < A ↔ D / (2 * A) < ε
  have hdenε : 0 < 2 * ε := by positivity
  have hdenA : 0 < 2 * A := by positivity
  constructor
  · intro h
    have hmul : D < A * (2 * ε) := by
      have hdiv := (div_lt_iff₀ hdenε).mp (show D / (2 * ε) < A by
        convert h using 1 <;> field_simp [ne_of_gt hε])
      linarith
    apply (div_lt_iff₀ hdenA).2
    nlinarith
  · intro h
    have hmul : D < ε * (2 * A) := (div_lt_iff₀ hdenA).mp h
    have hdiv : D / (2 * ε) < A := (div_lt_iff₀ hdenε).2 (by nlinarith)
    convert hdiv using 1 <;> field_simp [ne_of_gt hε]

end InfoGeometry.Inference
