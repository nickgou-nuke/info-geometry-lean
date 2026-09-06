import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# The associative `M₂(ℤ)` corner of the integral Zorn carrier

The full split-octonion multiplication is nonassociative.  The coordinates
`(a,b,x₀,y₀)` form a canonical associative corner, represented natively by
`2 × 2` matrices.  This owner isolates that fact from any later matrix readout.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.AssociativeCorner

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

abbrev Corner2 := Matrix (Fin 2) (Fin 2) ℤ

def cornerToSplit (A : Corner2) : SplitOct :=
  ⟨A 0 0, A 1 1, A 0 1, 0, 0, A 1 0, 0, 0⟩

def splitToCorner (X : SplitOct) : Corner2 :=
  fun i j =>
    if i = 0 ∧ j = 0 then X.a
    else if i = 0 ∧ j = 1 then X.x0
    else if i = 1 ∧ j = 0 then X.y0
    else X.b

def IsCorner (X : SplitOct) : Prop :=
  X.x1 = 0 ∧ X.x2 = 0 ∧ X.y1 = 0 ∧ X.y2 = 0

@[simp] theorem splitToCorner_cornerToSplit (A : Corner2) :
    splitToCorner (cornerToSplit A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitToCorner, cornerToSplit]

@[simp] theorem cornerToSplit_splitToCorner (X : SplitOct) (hX : IsCorner X) :
    cornerToSplit (splitToCorner X) = X := by
  rcases hX with ⟨hx1, hx2, hy1, hy2⟩
  ext <;> simp [cornerToSplit, splitToCorner, hx1, hx2, hy1, hy2]

theorem mulZ_cornerToSplit (A B : Corner2) :
    mulZ (cornerToSplit A) (cornerToSplit B) = cornerToSplit (A * B) := by
  ext <;>
    simp [cornerToSplit, mulZ, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem isCorner_cornerToSplit (A : Corner2) : IsCorner (cornerToSplit A) := by
  simp [IsCorner, cornerToSplit]

theorem isCorner_iff_splitToCorner_cornerToSplit (X : SplitOct) :
    IsCorner X ↔ cornerToSplit (splitToCorner X) = X := by
  constructor
  · exact cornerToSplit_splitToCorner X
  · intro h
    rw [← h]
    exact isCorner_cornerToSplit _

end InfoGeometry.OperatorAlgebra.SplitOctonions.AssociativeCorner
