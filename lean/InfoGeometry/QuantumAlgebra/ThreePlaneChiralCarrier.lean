import Mathlib
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
