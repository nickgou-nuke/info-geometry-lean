import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# Integral equivalence certificate for the twelve-vertex relation matrix

The constants are witnesses, not trusted oracle results. The equalities are
proved by `decide`, with no native_decide, external axiom, or determinant
expansion. Both inverse matrices are integral.
-/

namespace InfoGeometry.Canonical.SpinorialCore.G2
open Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

def cycle : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0]

def adjacency : Matrix (Fin 12) (Fin 12) ℤ :=
  !![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]

def relation : Matrix (Fin 12) (Fin 12) ℤ := 1 - adjacency

def blockIndex : Fin 6 ⊕ Fin 6 → Fin 12 :=
  Sum.elim (Fin.castAdd 6) (Fin.natAdd 6)

/-- The displayed certificate uses exactly the manuscript's block matrix. -/
theorem adjacency_eq_blocks :
    adjacency.submatrix blockIndex blockIndex =
      Matrix.fromBlocks cycle (1 + cycle ^ 5) (1 + cycle) cycle := by decide

theorem cycle_six : cycle ^ 6 = 1 := by decide

theorem row_sum_three : ∀ i : Fin 12, ∑ j, adjacency i j = 3 := by decide

theorem constant_vector_eigenvalue :
    adjacency *ᵥ (fun _ => (1 : ℤ)) = fun _ => (3 : ℤ) := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using row_sum_three i

def U : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     1, 2, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0;
     2, 5, 6, 6, 6, 0, 2, 1, 0, 0, 0, 0;
     0, 2, 4, 3, 2, 0, 0, 2, 0, -1, 0, 0;
     0, -2, -4, -2, -1, 0, 0, -2, 0, 2, -1, 0;
     1, -2, -7, 2, 5, 0, 1, -4, -1, 10, -7, 0;
     -14, -12, -4, 26, -26, -58, 9, -7, 15, 15, -67, 35;
     -29, -25, -9, 55, -53, -121, 19, -15, 31, 33, -141, 73]

def UInv : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     -1, -1, -1, -1, -1, 2, -2, -12, -26, 10, 73, -35;
     -1, -2, -2, -2, -2, 1, 0, 0, 0, 0, 0, 0;
     0, -1, -2, -2, -2, -2, 1, 0, 0, 0, 0, 0;
     0, 0, -1, -2, -2, -3, 2, 4, 7, -1, 0, 0;
     0, 0, 0, -1, -2, -4, 2, -1, 0, 0, 0, 0;
     0, 0, 0, 0, -1, -4, 2, -2, -1, 0, 0, 0;
     -1, -1, -1, -1, -1, -2, -1, -25, -48, 17, 121, -58]

def V : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, 1, 1, 1, 1, 0, 1, 13, 26, -19, -137, 11953;
     0, 1, 1, 1, 1, 0, 0, 2, 4, -3, -22, 1919;
     0, 0, 1, 1, 1, 1, -1, -5, -10, 7, 49, -4275;
     0, 0, 0, 1, 1, 2, -1, 0, 0, -1, -12, 1047;
     0, 0, 0, 0, 1, 2, -1, 1, 1, -1, -9, 785;
     0, 0, 0, 0, 0, 2, -1, 1, 0, 1, 10, -873;
     0, 0, 0, 0, 0, 0, 1, 11, 22, -16, -115, 10033;
     0, 0, 0, 0, 0, -1, 0, -4, -8, 6, 44, -3839;
     0, 0, 0, 0, 0, 0, 0, -1, -2, 2, 17, -1483;
     0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -20, 1745;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -87;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def VInv : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
     0, 1, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0;
     0, 0, 1, -1, 0, 0, 0, -1, -1, 0, 0, 0;
     0, 0, 0, 1, -1, 0, 0, 0, -1, -1, 0, 0;
     0, 0, 0, 0, 1, -1, 0, 0, 0, -1, -1, 0;
     0, 0, 0, 0, 0, -2, -2, -5, -4, -4, -2, -1;
     0, 0, 0, 0, 0, -6, -5, -12, -13, -12, -6, -2;
     0, 0, 0, 0, 0, -2, -2, -4, -9, -6, -1, 0;
     0, 0, 0, 0, 0, 2, 2, 4, 8, 5, -2, 1;
     0, 0, 0, 0, 0, 1, 1, 2, 4, 2, -11, 3;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 87;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def diagonalEntries : Fin 12 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 364]
def smithDiagonal : Matrix (Fin 12) (Fin 12) ℤ := Matrix.diagonal diagonalEntries

theorem U_mul_UInv : U * UInv = 1 := by decide
theorem UInv_mul_U : UInv * U = 1 := by decide
theorem V_mul_VInv : V * VInv = 1 := by decide
theorem VInv_mul_V : VInv * V = 1 := by decide

/-- Exact integral two-sided equivalence with the claimed Smith diagonal. -/
theorem smith_certificate : U * relation * V = smithDiagonal := by decide

theorem diagonal_nonzero : ∀ i, diagonalEntries i ≠ 0 := by decide

theorem diagonal_divisibility_chain :
    ∀ i : Fin 11, diagonalEntries i.castSucc ∣ diagonalEntries i.succ := by decide

/-- Product of the invariant factors, not a separately asserted determinant of U or V. -/
theorem diagonal_determinant : Matrix.det smithDiagonal = 1456 := by
  norm_num [smithDiagonal, Matrix.det_diagonal, diagonalEntries, Fin.prod_univ_succ]

end InfoGeometry.Canonical.SpinorialCore.G2
