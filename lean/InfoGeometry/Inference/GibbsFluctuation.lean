/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference

/-!
# Gibbs fluctuation pressure

This module formalizes the scalar part of the information-geometric curvature
decomposition. The fluctuation term is a weighted variance divided by the
positive temperature; the exact scalar curvature is defined as stiffness minus
fluctuation pressure.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

/-- Weighted mean of a scalar observable. -/
noncomputable def weightedMean (w f : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * f i

/-- Weighted variance around the weighted mean. -/
noncomputable def weightedVariance (w f : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * (f i - weightedMean w f) ^ 2

theorem weightedVariance_nonneg
    (w f : Data → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ weightedVariance w f := by
  unfold weightedVariance
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sq_nonneg _)

/-- Weighted scalar stiffness, supplied by the per-observation curvature. -/
noncomputable def fisherStiffness (w h₂ : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * h₂ i

/-- Fluctuation pressure at temperature `ε`. -/
noncomputable def fluctuationPressure (w f : Data → ℝ) (ε : ℝ) : ℝ :=
  weightedVariance w f / ε

/-- Exact scalar curvature in the `A - B` decomposition. -/
noncomputable def exactScalarHessian
    (w h₂ f : Data → ℝ) (ε : ℝ) : ℝ :=
  fisherStiffness w h₂ - fluctuationPressure w f ε

theorem fluctuationPressure_nonneg
    (w f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ fluctuationPressure w f ε := by
  unfold fluctuationPressure
  exact div_nonneg (weightedVariance_nonneg w f hw) hε.le

theorem gibbsFluctuationPressure_nonneg
    {Theta : Type*} [Nonempty Data]
    (M : FiniteGibbs.Model (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (hε : 0 < ε) (f : Data → ℝ) :
    0 ≤ fluctuationPressure (FiniteGibbs.weight M θ ε) f ε := by
  exact fluctuationPressure_nonneg
    (FiniteGibbs.weight M θ ε) f ε hε
    (fun i => (FiniteGibbs.weight_pos M θ ε i).le)

end InfoGeometry.Inference
