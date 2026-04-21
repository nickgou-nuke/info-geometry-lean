import InfoGeometry.Convex.Euclidean
import Mathlib.Analysis.InnerProductSpace.Basic

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The gradient map of the Euclidean quadratic potential is monotone:
  0 ≤ ⟪grad x - grad y, x - y⟫
This is a direct consequence of the parallelogram law and positivity of the squared norm.
-/
lemma euclidean_grad_monotone (x y : E) :
  0 ≤ inner ℝ (grad x - grad y) (x - y) :=
by
  -- grad x = x, grad y = y
  simp [grad]
  -- inner (x - y) (x - y) = ∥x - y∥^2 ≥ 0
  exact real_inner_self_nonneg _
