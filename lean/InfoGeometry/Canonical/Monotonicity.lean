import InfoGeometry.Convex.EuclideanMonotonicity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
The Euclidean gradient monotonicity specialization re-exported from the convex
owner file.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
None.
-/

namespace InfoGeometry.Canonical.Monotonicity

open InfoGeometry.Convex
open InfoGeometry.Convex.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem euclidean_gradient_monotone (x y : E) : 0 ≤ inner ℝ (grad x - grad y) (x - y) :=
  euclidean_grad_monotone x y

end InfoGeometry.Canonical.Monotonicity
