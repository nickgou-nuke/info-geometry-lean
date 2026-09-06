import InfoGeometry.Analysis.SouriauThermodynamics

/-!
# InfoGeometry.Analysis.SouriauCocycle

Repaired finite cocycle baseline salvaged from deleted Souriau files.

The deleted file asserted a nontrivial symplectic 2-cocycle without a proof.
This repaired file keeps only kernel-checked algebraic facts:

* the standard `2 × 2` symplectic matrix `J`;
* `J² = -I`;
* the zero 2-cocycle baseline and its Jacobi identity.

No nonzero Souriau anomaly cocycle is claimed here.
-/

namespace InfoGeometry.Analysis

open Matrix

/-- The standard two-dimensional symplectic matrix. -/
noncomputable def J_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

/-- The standard symplectic matrix squares to `-I`. -/
theorem J_matrix_sq_eq_neg_one :
    J_matrix * J_matrix = - (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals norm_num [J_matrix]

/-- The honest zero baseline for a bilinear 2-cocycle slot. -/
noncomputable def zero_symplectic_2_cocycle (_X _Y : SL2cAlgebra) : ℂ :=
  0

/-- The zero 2-cocycle satisfies the cyclic Jacobi cocycle identity. -/
theorem zero_symplectic_2_cocycle_jacobi_identity
    (X Y Z : SL2cAlgebra) :
    zero_symplectic_2_cocycle X Y + zero_symplectic_2_cocycle Y Z +
      zero_symplectic_2_cocycle Z X = 0 := by
  simp [zero_symplectic_2_cocycle]

end InfoGeometry.Analysis
