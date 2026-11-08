import InfoGeometry.Modular.WeylPfaffianDeterminantTriple
import Mathlib.Tactic

/-!
# Determinant and ratio identity for two matrix sectors

The positive scale/sign decomposition of a nonzero real determinant is owned
by `InfoGeometry.Volume.RealUnitScaleParity`. The quotient
`det A / det D` in this file is a determinant ratio (the block-diagonal
Berezinian formula), not a unit-circle phase. The theorem below records the
exact cancellation relating that ratio to the product determinant.
-/

namespace InfoGeometry.Modular.DeterminantTrifactorHomomorphism

open Matrix
open InfoGeometry.Modular.Triple

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplying the product determinant by the determinant ratio cancels the
second sector and gives the square of the first-sector determinant. -/
theorem totalDet_mul_berezinian_eq_det_sq
    {F : Type*} [Field F] (A D : Matrix ι ι F)
    (hD : Matrix.det D ≠ 0) :
    totalDet A D * berezinian A D = (Matrix.det A) ^ 2 := by
  dsimp [totalDet, berezinian]
  field_simp [hD]

end InfoGeometry.Modular.DeterminantTrifactorHomomorphism
