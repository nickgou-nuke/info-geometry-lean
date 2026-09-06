/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelFamily

/-!
# Simplex geometry of finite Gibbs model assignments

For each observation, the model responsibilities form a point in the finite
probability simplex. Positive priors and finite temperature place that point in
the strict interior; concentration near faces is an asymptotic or thresholded
notion, not an exact finite-temperature zero.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

def inProbabilitySimplex (w : ModelId → ℝ) : Prop :=
  (∀ m, 0 ≤ w m) ∧ ∑ m : ModelId, w m = 1

def inStrictProbabilitySimplex (w : ModelId → ℝ) : Prop :=
  (∀ m, 0 < w m) ∧ ∑ m : ModelId, w m = 1

noncomputable def responsibilityVector
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) : ModelId → ℝ :=
  fun m => responsibility F ε m i

theorem responsibilityVector_inProbabilitySimplex
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    inProbabilitySimplex (responsibilityVector F ε i) := by
  constructor
  · intro m
    exact responsibility_nonneg F ε m i
  · exact responsibilities_sum_one F ε i

theorem responsibilityVector_inStrictProbabilitySimplex
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    inStrictProbabilitySimplex (responsibilityVector F ε i) := by
  constructor
  · intro m
    exact responsibility_pos F ε m i
  · exact responsibilities_sum_one F ε i

theorem responsibilityVector_is_simplex_point
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    inProbabilitySimplex (responsibilityVector F ε i) :=
  responsibilityVector_inProbabilitySimplex F ε i

end InfoGeometry.Inference.FiniteGibbs
