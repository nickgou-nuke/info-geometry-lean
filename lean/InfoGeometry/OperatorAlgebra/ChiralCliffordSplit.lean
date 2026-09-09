import InfoGeometry.Canonical.ZornCliffordRepresentation

/-!
# Chiral Clifford Split Algebra

This module formalizes the algebraic relations for the vector/chiral splitting
within the Zorn matrix representation.

Specifically, it proves:
1. `zornConj_eq_neg_of_diagonal_zero`: If a Zorn matrix has zero diagonal elements
   (representing a pure spatial vector in the De Witt split), its Zorn conjugation
   is exactly its negation.
2. `vector_neg_mul`: The algebraic relation for multiplying negation components.
3. `vector_clifford_relation`: The vector Clifford relation for the Zorn matrix action
   on a spinor: $V \cdot (V \cdot S) = (V.x \cdot V.y) \cdot S$.

All proofs are native, formal Lean 4 derivations checked by the kernel with zero sorry debt.
-/

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford

variable {R : Type*} [CommRing R]

/-- Under the De Witt split, if the diagonal components a and b are zero,
    the Zorn conjugate of a matrix is equal to its negative. -/
theorem zornConj_eq_neg_of_diagonal_zero (V : ZornMatrix R) (ha : V.a = 0) (hb : V.b = 0) :
    zornConj V = -V := by
  apply ZornMatrix.ext
  · simp [zornConj, ha, hb]
  · simp [zornConj, ha, hb]
  · simp [zornConj]
  · simp [zornConj]

/-- Distributive negation rule for vector multiplication. -/
theorem vector_neg_mul (V S : ZornMatrix R) : V * (-V * S) = -(V * (V * S)) := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
    ring
  · simp [mul_def, mul, dot, cross]
    ring
  · ext i; fin_cases i <;>
      dsimp [ZornMatrix.mul_def, mul, dot, cross, Matrix.vecHead, Matrix.vecTail,
             Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;>
      ring
  · ext i; fin_cases i <;>
      dsimp [ZornMatrix.mul_def, mul, dot, cross, Matrix.vecHead, Matrix.vecTail,
             Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;>
      ring

/-- The main Clifford relation for the split Clifford algebra:
    $V \cdot (V \cdot S) = (V_x \cdot V_y) \cdot S$. -/
theorem vector_clifford_relation (V : ZornMatrix R) (ha : V.a = 0) (hb : V.b = 0) (S : ZornMatrix R) :
    V * (V * S) = (dot V.x V.y) • S := by
  have h1 : V * (zornConj V * S) = zornNormFun V • S := mul_zornConj_mul V S
  rw [zornConj_eq_neg_of_diagonal_zero V ha hb] at h1
  have h2 : zornNormFun V = -dot V.x V.y := by
    simp [zornNormFun, ha, hb]
  rw [h2] at h1
  rw [vector_neg_mul V S] at h1
  have h3 : (-dot V.x V.y) • S = -((dot V.x V.y) • S) := by
    simp
  rw [h3] at h1
  exact neg_inj.mp h1
