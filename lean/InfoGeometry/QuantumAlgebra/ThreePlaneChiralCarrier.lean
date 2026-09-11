import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Three-plane chiral carrier for split-octonion braiding

This module defines the three chiral planes
`Π_k = span{σ_k^+, σ_k^-} ≅ Cl(1,1)_k`
inside the real Zorn carrier `ZornCoord`.

Kernel-checked contents:
* `upperChiralBasis` / `lowerChiralBasis`: the two directions in each plane
* `upperChiralBasis_sq_zero` / `lowerChiralBasis_sq_zero`: nilpotency
* `mixed_sheet_contraction`: `(σ_i^+ * σ_j^-).a = δᵢⱼ`
* the complete four-way multiplication readback on the six basis elements
-/

namespace InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier

open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-! ## Chiral planes -/

/-- Upper chiral basis element in plane `k`: `σ_k^+ = U(e_k)`. -/
def upperChiralBasis (k : Fin 3) : ZornCoord :=
  upperVectorZorn (Vec3.basis k)

/-- Lower chiral basis element in plane `k`: `σ_k^- = L(e_k)`. -/
def lowerChiralBasis (k : Fin 3) : ZornCoord :=
  lowerVectorZorn (Vec3.basis k)

/-- Upper chiral basis elements are nilpotent: `(σ_k^+)^2 = 0`. -/
theorem upperChiralBasis_sq_zero (k : Fin 3) :
    zornMul (upperChiralBasis k) (upperChiralBasis k) = zornMk 0 0 0 0 := by
  unfold upperChiralBasis upperVectorZorn zornMul
  simp [zornMk, dot3, Vec3.basis]

/-- Lower chiral basis elements are nilpotent: `(σ_k^-)^2 = 0`. -/
theorem lowerChiralBasis_sq_zero (k : Fin 3) :
    zornMul (lowerChiralBasis k) (lowerChiralBasis k) = zornMk 0 0 0 0 := by
  unfold lowerChiralBasis lowerVectorZorn zornMul
  simp [zornMk, dot3, Vec3.basis]

/-- Mixed-sheet contraction on basis elements: `(σ_i^+ * σ_j^-).a = δᵢⱼ`. -/
theorem mixed_sheet_contraction (i j : Fin 3) :
    (zornMul (upperChiralBasis i) (lowerChiralBasis j)).1 =
      if i = j then (1 : ℝ) else (0 : ℝ) := by
  unfold upperChiralBasis lowerChiralBasis upperVectorZorn lowerVectorZorn
  fin_cases i <;> fin_cases j <;>
    simp [zornMul, dot3, Vec3.basis, zornMk]

/-! ## The six-generator multiplication table -/

theorem upperChiralBasis_mul_upperChiralBasis (i j : Fin 3) :
    zornMul (upperChiralBasis i) (upperChiralBasis j) =
      lowerVectorZorn (cross3 (Vec3.basis i) (Vec3.basis j)) := by
  exact upperVectorZorn_mul_upperVectorZorn _ _

theorem lowerChiralBasis_mul_lowerChiralBasis (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (lowerChiralBasis j) =
      upperVectorZorn (-(cross3 (Vec3.basis i) (Vec3.basis j))) := by
  exact lowerVectorZorn_mul_lowerVectorZorn _ _

theorem upperChiralBasis_mul_lowerChiralBasis (i j : Fin 3) :
    zornMul (upperChiralBasis i) (lowerChiralBasis j) =
      zornMk (dot3 (Vec3.basis i) (Vec3.basis j)) 0 0 0 := by
  exact upperVectorZorn_mul_lowerVectorZorn _ _

theorem lowerChiralBasis_mul_upperChiralBasis (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (upperChiralBasis j) =
      zornMk 0 (dot3 (Vec3.basis i) (Vec3.basis j)) 0 0 := by
  exact lowerVectorZorn_mul_upperVectorZorn _ _

/-! The mixed upper-to-lower products are the first diagonal matrix-unit
    channel, with the Kronecker delta as their complete Zorn readback. -/
theorem upperChiralBasis_mul_lowerChiralBasis_delta (i j : Fin 3) :
    zornMul (upperChiralBasis i) (lowerChiralBasis j) =
      if i = j then zornMk 1 0 0 0 else zornMk 0 0 0 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [upperChiralBasis_mul_lowerChiralBasis, dot3,
      Vec3.basis, zornMk]

/-! The reverse mixed products are the second diagonal matrix-unit channel. -/
theorem lowerChiralBasis_mul_upperChiralBasis_delta (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (upperChiralBasis j) =
      if i = j then zornMk 0 1 0 0 else zornMk 0 0 0 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [lowerChiralBasis_mul_upperChiralBasis, dot3,
      Vec3.basis, zornMk]

/-! The diagonal mixed products act as the corresponding matrix units. -/
theorem upperChiralBasis_mixed_action (i : Fin 3) :
    zornMul
        (zornMul (upperChiralBasis i) (lowerChiralBasis i))
        (upperChiralBasis i) = upperChiralBasis i := by
  fin_cases i <;>
    simp [upperChiralBasis, lowerChiralBasis, upperVectorZorn,
      lowerVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3, Vec3.basis,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    funext j <;> fin_cases j <;> rfl

theorem lowerChiralBasis_mixed_action (i : Fin 3) :
    zornMul
        (zornMul (lowerChiralBasis i) (upperChiralBasis i))
        (lowerChiralBasis i) = lowerChiralBasis i := by
  fin_cases i <;>
    simp [upperChiralBasis, lowerChiralBasis, upperVectorZorn,
      lowerVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3, Vec3.basis,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    funext j <;> fin_cases j <;> rfl

theorem upperChiralBasis_mixed_idempotent (i : Fin 3) :
    zornMul
        (zornMul (upperChiralBasis i) (lowerChiralBasis i))
        (zornMul (upperChiralBasis i) (lowerChiralBasis i)) =
      zornMul (upperChiralBasis i) (lowerChiralBasis i) := by
  fin_cases i <;>
    simp [upperChiralBasis, lowerChiralBasis, upperVectorZorn,
      lowerVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3, Vec3.basis, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    funext j <;> fin_cases j <;> rfl

theorem lowerChiralBasis_mixed_idempotent (i : Fin 3) :
    zornMul
        (zornMul (lowerChiralBasis i) (upperChiralBasis i))
        (zornMul (lowerChiralBasis i) (upperChiralBasis i)) =
      zornMul (lowerChiralBasis i) (upperChiralBasis i) := by
  fin_cases i <;>
    simp [upperChiralBasis, lowerChiralBasis, upperVectorZorn,
      lowerVectorZorn, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3, Vec3.basis, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    funext j <;> fin_cases j <;> rfl

theorem upperChiralBasis_mul_upperChiralBasis_antisymm (i j : Fin 3) :
    zornMul (upperChiralBasis i) (upperChiralBasis j) =
      -zornMul (upperChiralBasis j) (upperChiralBasis i) := by
  rw [upperChiralBasis_mul_upperChiralBasis,
    upperChiralBasis_mul_upperChiralBasis, cross3_swap]
  ext <;> simp [lowerVectorZorn, zornMk]

theorem lowerChiralBasis_mul_lowerChiralBasis_antisymm (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (lowerChiralBasis j) =
      -zornMul (lowerChiralBasis j) (lowerChiralBasis i) := by
  rw [lowerChiralBasis_mul_lowerChiralBasis,
    lowerChiralBasis_mul_lowerChiralBasis, cross3_swap]
  ext <;> simp [upperVectorZorn, zornMk]

/-! ## Fixed-bracketing triple and fourfold readbacks -/

theorem upperChiralBasis_triple_left (i j k : Fin 3) :
    zornMul (zornMul (upperChiralBasis i) (upperChiralBasis j))
        (upperChiralBasis k) =
      zornMk 0 (dot3 (cross3 (Vec3.basis i) (Vec3.basis j))
        (Vec3.basis k)) 0 0 := by
  rw [upperChiralBasis_mul_upperChiralBasis]
  change zornMul (lowerVectorZorn (cross3 (Vec3.basis i) (Vec3.basis j)))
      (upperVectorZorn (Vec3.basis k)) = _
  exact lowerVectorZorn_mul_upperVectorZorn (Vec3.basis k)
    (cross3 (Vec3.basis i) (Vec3.basis j))

theorem lowerChiralBasis_triple_left (i j k : Fin 3) :
    zornMul (zornMul (lowerChiralBasis i) (lowerChiralBasis j))
        (lowerChiralBasis k) =
      zornMk (dot3 (-(cross3 (Vec3.basis i) (Vec3.basis j)))
        (Vec3.basis k)) 0 0 0 := by
  rw [lowerChiralBasis_mul_lowerChiralBasis]
  change zornMul (upperVectorZorn (-(cross3 (Vec3.basis i) (Vec3.basis j))))
      (lowerVectorZorn (Vec3.basis k)) = _
  exact upperVectorZorn_mul_lowerVectorZorn
    (-(cross3 (Vec3.basis i) (Vec3.basis j))) (Vec3.basis k)

/-! The positively oriented three-plane contraction. -/
theorem upperChiralBasis_triple_012 :
    zornMul (zornMul (upperChiralBasis 0) (upperChiralBasis 1))
        (upperChiralBasis 2) = zornMk 0 1 0 0 := by
  rw [upperChiralBasis_triple_left]
  norm_num [dot3, cross3, Vec3.basis, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, zornMk,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

/-! The reverse-sheet contraction carries the opposite orientation sign. -/
theorem lowerChiralBasis_triple_012 :
    zornMul (zornMul (lowerChiralBasis 0) (lowerChiralBasis 1))
        (lowerChiralBasis 2) = zornMk (-1) 0 0 0 := by
  rw [lowerChiralBasis_triple_left]
  norm_num [dot3, cross3, Vec3.basis, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, zornMk,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem upperChiralBasis_fourfold_left (i j k l : Fin 3) :
    zornMul
        (zornMul (zornMul (upperChiralBasis i) (upperChiralBasis j))
          (upperChiralBasis k)) (upperChiralBasis l) =
      zornMk 0 0 0 0 := by
  rw [upperChiralBasis_triple_left]
  simp [zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3,
    upperChiralBasis, upperVectorZorn, Vec3.basis]

theorem lowerChiralBasis_fourfold_left (i j k l : Fin 3) :
    zornMul
        (zornMul (zornMul (lowerChiralBasis i) (lowerChiralBasis j))
          (lowerChiralBasis k)) (lowerChiralBasis l) =
      zornMk 0 0 0 0 := by
  rw [lowerChiralBasis_triple_left]
  simp [zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3,
    lowerChiralBasis, lowerVectorZorn, Vec3.basis]

end InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier
