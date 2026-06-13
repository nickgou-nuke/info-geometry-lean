import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.OperatorAlgebra.FibonacciBoundary

/-- 
The intrinsic Fibonacci adjacency matrix linking the trivial (1) and tau (τ) sectors.
-/
def fibonacciAdjacency : Matrix (Fin 2) (Fin 2) ℕ := ![![0, 1], ![1, 1]]

/-- 
The null topological path boundary of admissible Fibonacci fusion paths.
This serves as the Cantor-Cuntz-Krieger boundary O_A. 
-/
def AdmissiblePathSpace :=
  { x : ℕ → Fin 2 // ∀ i, fibonacciAdjacency (x i) (x (i + 1)) = 1 }

/-- 
Fibonacci path-count recursion.
Maps the growth of admissible paths onto the null boundaries.
-/
def fibonacciPathCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibonacciPathCount (n + 1) + fibonacciPathCount n

end InfoGeometry.OperatorAlgebra.FibonacciBoundary
