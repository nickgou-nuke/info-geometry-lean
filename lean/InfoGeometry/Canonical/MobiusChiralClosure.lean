import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MobiusChiralClosure

open Matrix

/-!
# Möbius Supergrading and Chiral Closure

The chiral charge and Möbius-twisted charge both have vanishing trace.
This is an algebraic cancellation: the diagonal entries sum to zero pairwise.
-/

/-- The 4x4 global chiral charge for Cl(2,2): diag(1, -1, -1, 1). -/
def chi_global_4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, 1]

/-- The Möbius twist parity operator: diag(1, -1, 1, -1). -/
def moebius_strip_4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- The global chiral charge has zero trace because the diagonal entries
(1, -1, -1, 1) cancel pairwise.  4×4 finite computation. -/
theorem global_chiral_balance_4 :
    Matrix.trace chi_global_4 = 0 := by
  rw [Matrix.trace, Fin.sum_univ_four]
  simp [chi_global_4]

/-- The Möbius-twisted charge also has zero trace.  Both matrices are diagonal
so the product entries are (1·1, -1·-1, -1·1, 1·-1) = (1, 1, -1, -1), summing
to zero.  4×4 finite computation. -/
theorem moebius_parity_closure_achieved_4 :
    Matrix.trace (moebius_strip_4 * chi_global_4) = 0 := by
  rw [Matrix.trace, Fin.sum_univ_four]
  simp [moebius_strip_4, chi_global_4]

end MobiusChiralClosure
