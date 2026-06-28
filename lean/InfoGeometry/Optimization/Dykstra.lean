/- Dykstra Projection for Birkhoff Retraction -/
/- Alternating projection algorithm to retract a matrix onto the Birkhoff Polytope
   (doubly stochastic matrices with row/column sums = 1 and non-negative entries). -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Basic

open Matrix
open scoped Matrix BigOperators

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Project onto the row-stochastic constraint (rows sum to 1). -/
noncomputable def ProjectRow (M : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => M i j / (∑ k : n, M i k)

/-- Project onto the column-stochastic constraint (columns sum to 1). -/
noncomputable def ProjectCol (M : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => M i j / (∑ k : n, M k j)

/-- 
  One step of Dykstra's Alternating Projection Algorithm.
  Takes the current matrix X, and the residual increment matrices P and Q.
-/
noncomputable def DykstraStep (X P Q : Matrix n n ℝ) : Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ :=
  let Y := ProjectRow (X + P)
  let P_new := X + P - Y
  let X_new := ProjectCol (Y + Q)
  let Q_new := Y + Q - X_new
  (X_new, P_new, Q_new)

/-- Recursive application of the Dykstra sequence. -/
noncomputable def DykstraSeq : ℕ → Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ → Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ
  | 0, state => state
  | k + 1, (X, P, Q) => DykstraSeq k (DykstraStep X P Q)

/-- The final metric retraction onto the Birkhoff Polytope. -/
noncomputable def BirkhoffRetraction (M : Matrix n n ℝ) (iters : ℕ) : Matrix n n ℝ :=
  (DykstraSeq iters (M, 0, 0)).1

end InfoGeometry.Optimization