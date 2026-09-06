import InfoGeometry.Convex.EuclideanMonotonicity

open InfoGeometry.Convex
open InfoGeometry.Convex.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

#check euclidean_grad_monotone

example (x y : E) : 0 ≤ inner ℝ (grad x - grad y) (x - y) := euclidean_grad_monotone x y
