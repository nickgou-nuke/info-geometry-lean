import InfoGeometry.Convex.Euclidean
import Mathlib.Analysis.InnerProductSpace.Basic

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/--
The gradient map of the Euclidean quadratic potential is monotone:
  0 ≤ ⟪grad x - grad y, x - y⟫
This is a direct consequence of the parallelogram law and positivity of the squared norm.
-/
theorem euclidean_grad_monotone (x y : E) :
  0 ≤ inner ℝ
    (InfoGeometry.Convex.Euclidean.grad x - InfoGeometry.Convex.Euclidean.grad y)
    (x - y) :=
by
  -- grad x = x, grad y = y
  simp [InfoGeometry.Convex.Euclidean.grad]
