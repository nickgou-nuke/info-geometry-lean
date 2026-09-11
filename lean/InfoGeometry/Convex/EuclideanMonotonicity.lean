import InfoGeometry.Convex.Euclidean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic

namespace InfoGeometry.Convex

open InfoGeometry.Convex.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The gradient map of the Euclidean quadratic potential is monotone:
  0 ≤ ⟪grad x - grad y, x - y⟫
This is a direct consequence of the parallelogram law and positivity of the squared norm.
-/
lemma euclidean_grad_monotone (x y : E) :
  0 ≤ inner ℝ (grad x - grad y) (x - y) := by
  -- grad x = x, grad y = y; goal reduces to nonnegativity of `⟪x - y, x - y⟫`
  simp [grad]

end InfoGeometry.Convex
