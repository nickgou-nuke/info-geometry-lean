import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.OperatorAlgebra.ColeFuryIdeals
import Mathlib.Data.Matrix.Basic

/-!
# Cole-Fury 32x32 Embedding of Split Octonion Ideals

This module embeds the 8-dimensional Split Octonion algebra into the 32x32 Cole-Fury
spinor matrix blocks. Because Split Octonions are non-associative and `Spin32Matrix`
is an associative matrix algebra, a general algebra homomorphism is mathematically
impossible (e.g., `up0 * up1 = down2` but `horizonUp * horizonUp = 0`).

To maintain strict theorem-honesty (Pauli Mandate), we implement the embedding as
a linear projection and rigorously prove that `mulZ` maps to `*` precisely on the
associative "First Generation" (2x2) subspace where non-associative cross terms vanish.
-/

namespace InfoGeometry.OperatorAlgebra.ColeFury

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open Matrix

/--
Embedding of the 8D Split Octonion algebra into the 32x32 Cole-Fury spinor block matrices.
- `ePlus` (a) maps to `upperLeft`
- `eMinus` (b) maps to `lowerRight`
- The `up_i` coordinates project aggregately to `horizonUp`
- The `down_i` coordinates project aggregately to `horizonDown`
-/
def embed (X : SplitOct) : Spin32Matrix :=
  X.a • upperLeft + X.b • lowerRight +
  (X.x0 + X.x1 + X.x2) • horizonUp +
  (X.y0 + X.y1 + X.y2) • horizonDown

/--
A predicate restricting a Split Octonion to the associative 2x2 subalgebra,
where the cross-product components vanish.
-/
def isAssociativeSubalgebra (X : SplitOct) : Prop :=
  X.x1 = 0 ∧ X.x2 = 0 ∧ X.y1 = 0 ∧ X.y2 = 0

private theorem upperLeft_horizonUp : upperLeft * horizonUp = horizonUp := by unfold upperLeft horizonUp; native_decide
private theorem upperLeft_horizonDown : upperLeft * horizonDown = 0 := by unfold upperLeft horizonDown; native_decide
private theorem horizonUp_upperLeft : horizonUp * upperLeft = 0 := by unfold upperLeft horizonUp; native_decide
private theorem horizonDown_upperLeft : horizonDown * upperLeft = horizonDown := by unfold upperLeft horizonDown; native_decide

private theorem lowerRight_horizonUp : lowerRight * horizonUp = 0 := by unfold lowerRight horizonUp; native_decide
private theorem lowerRight_horizonDown : lowerRight * horizonDown = horizonDown := by unfold lowerRight horizonDown; native_decide
private theorem horizonUp_lowerRight : horizonUp * lowerRight = horizonUp := by unfold lowerRight horizonUp; native_decide
private theorem horizonDown_lowerRight : horizonDown * lowerRight = 0 := by unfold lowerRight horizonDown; native_decide

/--
The embedding perfectly maps Split Octonion multiplication (`mulZ`) to matrix
multiplication (`*`) on the associative subalgebra.
(Theorem-honesty: We explicitly gate this to `isAssociativeSubalgebra` to avoid
falsely claiming non-associative closure inside associative matrices).
-/
theorem embed_mulZ_associative (X Y : SplitOct) 
    (hX : isAssociativeSubalgebra X) (hY : isAssociativeSubalgebra Y) :
    embed (mulZ X Y) = embed X * embed Y := by
  dsimp [isAssociativeSubalgebra] at hX hY
  rcases hX with ⟨hx1, hx2, hy1, hy2⟩
  rcases hY with ⟨hyx1, hyx2, hyy1, hyy2⟩
  dsimp [embed, mulZ]
  rw [hx1, hx2, hy1, hy2, hyx1, hyx2, hyy1, hyy2]
  simp only [zero_mul, mul_zero, sub_zero, add_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [upperLeft_idempotent, lowerRight_idempotent]
  rw [upperLeft_lowerRight_zero, lowerRight_upperLeft_zero]
  rw [horizonUp_horizonDown, horizonDown_horizonUp]
  rw [horizonUp_nilpotent, horizonDown_nilpotent]
  rw [upperLeft_horizonUp, upperLeft_horizonDown]
  rw [horizonUp_upperLeft, horizonDown_upperLeft]
  rw [lowerRight_horizonUp, lowerRight_horizonDown]
  rw [horizonUp_lowerRight, horizonDown_lowerRight]
  simp only [smul_zero, add_zero, zero_add, add_smul]
  ext i j
  simp [Matrix.add_apply, mul_comm, mul_assoc]
  ring

end InfoGeometry.OperatorAlgebra.ColeFury
