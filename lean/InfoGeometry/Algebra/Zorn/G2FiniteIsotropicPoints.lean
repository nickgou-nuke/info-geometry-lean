import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finset.Basic

/-!
# The nonzero isotropic points of the split Zorn carrier over `𝔽₂`

This file deliberately formalizes points only.  The full eight-dimensional
Zorn carrier has 135 nonzero isotropic elements; the 63-point geometry needs
the separate seven-dimensional imaginary/trace-zero carrier.  The 189
incident flags are a further, separate object.
-/

namespace InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- The quadratic norm of the split Zorn octonion over `𝔽₂`. -/
def zornNorm (X : SplitOctF2) : Bool :=
  Bool.xor (mul2 X.a X.b) (dot3 X.x0 X.x1 X.x2 X.y0 X.y1 X.y2)

/-- A carrier element is isotropic when its quadratic norm vanishes. -/
def Isotropic (X : SplitOctF2) : Prop := zornNorm X = false

/-- The zero element of the split Zorn carrier. -/
def zeroPoint : SplitOctF2 := zero

instance : DecidablePred (fun X : SplitOctF2 => Isotropic X ∧ X ≠ zeroPoint) := by
  intro X
  unfold Isotropic
  infer_instance

/-- The finite set of nonzero isotropic points. -/
def isotropicPoints : Finset SplitOctF2 :=
  Finset.univ.filter (fun X => Isotropic X ∧ X ≠ zeroPoint)

theorem isotropicPoints_card : isotropicPoints.card = 135 := by
  native_decide

theorem mem_isotropicPoints (X : SplitOctF2) :
    X ∈ isotropicPoints ↔ Isotropic X ∧ X ≠ zeroPoint := by
  simp [isotropicPoints]

theorem isotropicPoints_nonempty : isotropicPoints.Nonempty := by
  exact Finset.card_pos.mp (by rw [isotropicPoints_card]; decide)

end InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
