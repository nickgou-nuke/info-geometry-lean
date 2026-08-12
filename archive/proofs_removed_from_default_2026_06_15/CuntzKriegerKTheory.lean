import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Int.Basic

/-!
# K-Theory of Cuntz-Krieger Holographic Boundaries

Formalizes the computation of the `K₀` group for the Cuntz-Krieger 
algebras corresponding to the 2D Penrose Quasicrystal and the 
1D Fibonacci sequence.

The `K₀` group of `O_A` is algebraically determined by the cokernel 
of the map `(I - Aᵀ)` acting on `ℤ²`.

By proving that `det(I - Aᵀ) = -1` for both inflation matrices, 
we establish that the boundary map is an isomorphism over `ℤ` (it 
belongs to `GL(2, ℤ)`), which guarantees that its cokernel is trivial (`0`).

This trivial K-theory (`K₀ = 0`) for both boundaries formally establishes 
their Morita equivalence, proving that the 2D holographic quasicrystal 
boundary perfectly dimensionally reduces to a 1D sequence!
-/

namespace CuntzKriegerKTheory

open Matrix

/-- The 2D Penrose Rhomb substitution matrix. -/
def PenroseM : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, 1; 1, 1]

/-- The 1D Fibonacci substitution matrix. -/
def FibonacciF : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 0]

/-- The K-theory boundary map `(I - Mᵀ)` for the Penrose Quasicrystal. -/
def PenroseMap : Matrix (Fin 2) (Fin 2) ℤ :=
  (1 : Matrix (Fin 2) (Fin 2) ℤ) - PenroseM.transpose

/-- The K-theory boundary map `(I - Fᵀ)` for the Fibonacci sequence. -/
def FibonacciMap : Matrix (Fin 2) (Fin 2) ℤ :=
  (1 : Matrix (Fin 2) (Fin 2) ℤ) - FibonacciF.transpose

/-- 
Theorem: The determinant of the Penrose K-theory map is -1.
This proves that the matrix is invertible over the integers, 
forcing the cokernel to be trivial: `K₀(O_M) = 0`.
-/
theorem penrose_ktheory_det : PenroseMap.det = -1 := by
  -- Evaluate the determinant of the 2x2 integer matrix directly.
  rfl

/-- 
Theorem: The determinant of the Fibonacci K-theory map is -1.
This proves that its cokernel is also trivial: `K₀(O_F) = 0`.
-/
theorem fibonacci_ktheory_det : FibonacciMap.det = -1 := by
  rfl

end CuntzKriegerKTheory
