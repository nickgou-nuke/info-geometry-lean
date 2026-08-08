import Mathlib

/-!
# Braid monodromy and the square-zero spectral defect

For a two-by-two matrix over a commutative ring, the trace and determinant
conditions for a repeated scalar root imply that the shifted matrix is
square-zero.  This is the finite Cayley--Hamilton bridge only; it does not
identify a particular braid word with a Jordan matrix without an additional
equality property.
-/

namespace InfoGeometry.Canonical

open Matrix

variable {K : Type*} [CommRing K]

theorem degenerate_eigenvalue_nilpotency
    (M : Matrix (Fin 2) (Fin 2) K) (lambda : K)
    (h_trace : M 0 0 + M 1 1 = 2 * lambda)
    (h_det : M 0 0 * M 1 1 - M 0 1 * M 1 0 = lambda ^ 2) :
    let N := M - !![lambda, 0; 0, lambda]
    N * N = 0 := by
  intro N
  have h_tr : M 1 1 = 2 * lambda - M 0 0 := by
    linear_combination h_trace
  have h_dt : M 0 1 * M 1 0 = M 0 0 * M 1 1 - lambda ^ 2 := by
    linear_combination -h_det
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
  all_goals
    first
    | linear_combination h_dt + M 0 0 * h_trace
    | linear_combination h_dt + M 1 1 * h_trace
    | linear_combination M 0 1 * h_trace
    | linear_combination M 1 0 * h_trace

end InfoGeometry.Canonical
