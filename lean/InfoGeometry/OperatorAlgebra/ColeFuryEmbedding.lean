import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ColeFuryIdeals
import Mathlib.Data.Matrix.Basic

/-!
# Cole-Fury 32x32 aggregate readout of the split-octonion carrier

This module projects the 8-dimensional Split Octonion algebra to the 32x32 Cole-Fury
spinor matrix blocks. Because Split Octonions are non-associative and `Spin32Matrix`
is an associative matrix algebra, a general algebra homomorphism is mathematically
impossible (e.g., `up0 * up1 = down2` but `horizonUp * horizonUp = 0`).

To maintain strict theorem-honesty, we implement an aggregate linear readout
and rigorously prove that `mulZ` maps to `*` on the
associative "First Generation" (2x2) subspace where non-associative cross terms vanish.
-/

namespace InfoGeometry.OperatorAlgebra.ColeFury

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open Matrix

/--
Aggregate linear readout of the 8D Split Octonion algebra to the 32x32 Cole-Fury spinor block matrices.
- `ePlus` (a) maps to `upperLeft`
- `eMinus` (b) maps to `lowerRight`
- The `up_i` coordinates project aggregately to `horizonUp`
- The `down_i` coordinates project aggregately to `horizonDown`
-/
def quadrantReadout (X : SplitOct) : Spin32Matrix :=
  X.a • upperLeft + X.b • lowerRight +
  (X.x0 + X.x1 + X.x2) • horizonUp +
  (X.y0 + X.y1 + X.y2) • horizonDown

/-- Compatibility name for the aggregate readout; this map is not injective. -/
abbrev embed := quadrantReadout

theorem embed_zero : embed (0 : SplitOct) = 0 := by
  change (0 : ℤ) • upperLeft + (0 : ℤ) • lowerRight + (0 : ℤ) • horizonUp + (0 : ℤ) • horizonDown = 0
  simp only [zero_smul, add_zero]

attribute [simp] embed_zero

theorem embed_add (X Y : SplitOct) : embed (X + Y) = embed X + embed Y := by
  change quadrantReadout (X + Y) = quadrantReadout X + quadrantReadout Y
  simp only [quadrantReadout, add_a, add_b, add_x0, add_x1, add_x2, add_y0,
    add_y1, add_y2, add_smul]
  abel

/-! The aggregate horizon coordinates make `embed` a readout, not an
injective embedding of the eight-dimensional Zorn carrier. -/

def kernelElement : SplitOct :=
  ⟨0, 0, 0, 1, -1, 0, 0, 0⟩

theorem kernelElement_ne_zero : kernelElement ≠ (0 : SplitOct) := by
  intro h
  have hcoord := congrArg SplitOct.x1 h
  change (1 : ℤ) = 0 at hcoord
  norm_num at hcoord

theorem embed_kernelElement : embed kernelElement = embed (0 : SplitOct) := by
  rw [embed_zero]
  change (0 : ℤ) • upperLeft + (0 : ℤ) • lowerRight + (0 + 1 + -1 : ℤ) • horizonUp + (0 : ℤ) • horizonDown = 0
  have h : (0 + 1 + -1 : ℤ) = 0 := by decide
  rw [h]
  simp only [zero_smul, add_zero]

theorem embed_not_injective : ¬ Function.Injective embed := by
  intro hinj
  apply kernelElement_ne_zero
  apply hinj
  simpa using embed_kernelElement

theorem quadrantReadout_not_injective : ¬ Function.Injective quadrantReadout := by
  exact embed_not_injective

/--
A predicate restricting a Split Octonion to the associative 2x2 subalgebra,
where the cross-product components vanish.
-/
def isAssociativeSubalgebra (X : SplitOct) : Prop :=
  X.x1 = 0 ∧ X.x2 = 0 ∧ X.y1 = 0 ∧ X.y2 = 0

private theorem horizonUp_upperLeft : horizonUp * upperLeft = 0 := by
  calc
    horizonUp * upperLeft = horizonUp * (horizonUp * horizonDown) := by rw [horizonUp_horizonDown]
    _ = (horizonUp * horizonUp) * horizonDown := by rw [mul_assoc]
    _ = 0 * horizonDown := by rw [horizonUp_nilpotent]
    _ = 0 := by rw [zero_mul]

private theorem lowerRight_horizonUp : lowerRight * horizonUp = 0 := by
  calc
    lowerRight * horizonUp = (horizonDown * horizonUp) * horizonUp := by rw [horizonDown_horizonUp]
    _ = horizonDown * (horizonUp * horizonUp) := by rw [mul_assoc]
    _ = horizonDown * 0 := by rw [horizonUp_nilpotent]
    _ = 0 := by rw [mul_zero]

private theorem upperLeft_horizonDown : upperLeft * horizonDown = 0 := by
  calc
    upperLeft * horizonDown = (horizonUp * horizonDown) * horizonDown := by rw [horizonUp_horizonDown]
    _ = horizonUp * (horizonDown * horizonDown) := by rw [mul_assoc]
    _ = horizonUp * 0 := by rw [horizonDown_nilpotent]
    _ = 0 := by rw [mul_zero]

private theorem horizonDown_lowerRight : horizonDown * lowerRight = 0 := by
  calc
    horizonDown * lowerRight = horizonDown * (horizonDown * horizonUp) := by rw [horizonDown_horizonUp]
    _ = (horizonDown * horizonDown) * horizonUp := by rw [mul_assoc]
    _ = 0 * horizonUp := by rw [horizonDown_nilpotent]
    _ = 0 := by rw [zero_mul]

private theorem upperLeft_horizonUp : upperLeft * horizonUp = horizonUp := by
  have hsum : upperLeft + lowerRight = 1 := diagonal_quadrants_sum
  have h : (upperLeft + lowerRight) * horizonUp = 1 * horizonUp := by rw [hsum]
  rw [add_mul, lowerRight_horizonUp, add_zero, one_mul] at h
  exact h

private theorem horizonDown_upperLeft : horizonDown * upperLeft = horizonDown := by
  have hsum : upperLeft + lowerRight = 1 := diagonal_quadrants_sum
  have h : horizonDown * (upperLeft + lowerRight) = horizonDown * 1 := by rw [hsum]
  rw [mul_add, horizonDown_lowerRight, add_zero, mul_one] at h
  exact h

private theorem lowerRight_horizonDown : lowerRight * horizonDown = horizonDown := by
  have hsum : upperLeft + lowerRight = 1 := diagonal_quadrants_sum
  have h : (upperLeft + lowerRight) * horizonDown = 1 * horizonDown := by rw [hsum]
  rw [add_mul, upperLeft_horizonDown, zero_add, one_mul] at h
  exact h

private theorem horizonUp_lowerRight : horizonUp * lowerRight = horizonUp := by
  have hsum : upperLeft + lowerRight = 1 := diagonal_quadrants_sum
  have h : horizonUp * (upperLeft + lowerRight) = horizonUp * 1 := by rw [hsum]
  rw [mul_add, horizonUp_upperLeft, zero_add, mul_one] at h
  exact h

/--
The aggregate readout maps split-octonion multiplication (`mulZ`) to matrix
multiplication on the associative corner.
(Theorem-honesty: We explicitly gate this to `isAssociativeSubalgebra` to avoid
falsely claiming non-associative closure inside associative matrices).
-/
theorem embed_mulZ_associative (X Y : SplitOct) 
    (hX : isAssociativeSubalgebra X) (hY : isAssociativeSubalgebra Y) :
    embed (mulZ X Y) = embed X * embed Y := by
  dsimp [isAssociativeSubalgebra] at hX hY
  rcases hX with ⟨hx1, hx2, hy1, hy2⟩
  rcases hY with ⟨hyx1, hyx2, hyy1, hyy2⟩
  change quadrantReadout (mulZ X Y) = quadrantReadout X * quadrantReadout Y
  dsimp [quadrantReadout, mulZ]
  rw [hx1, hx2, hy1, hy2, hyx1, hyx2, hyy1, hyy2]
  simp only [zero_mul, mul_zero, sub_zero, add_zero, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
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
