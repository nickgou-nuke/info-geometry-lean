import InfoGeometry.Canonical.ThreeColorOperatorSuperBracketClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorValuedSuperconnection

noncomputable section

/-!
# Chiral coefficient channel for the graded superconnection

The primitive Zorn carrier is product-first and has no subtraction.  This
adapter therefore exposes only the already-proved odd--odd sum channel as the
coefficient term of a graded superconnection.  The ordinary difference channel
remains owned by the associative operator-valued connection layer.
-/

namespace InfoGeometry.Canonical.ChiralSuperconnectionCurvatureBridge

open InfoGeometry.Canonical

variable {A : Type*} [Ring A]

/-- The chiral graded coefficient is the existing odd--odd closure. -/
def chiralGradedCoefficient
    (U V : OperatorVector A) : OperatorZornMatrix A :=
  oddOddSuperBracket (sigmaPlus U) (sigmaMinus V)

/-- Explicit identification with the two even diagonal channels. -/
theorem chiral_gradedWedgeSquare_eq_nPlus_add_nMinus
    (U V : OperatorVector A) :
    chiralGradedCoefficient U V =
      operatorAdd (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  exact sigmaPlus_superBracket_sigmaMinus U V

/-- The coefficient is definitionally the odd--odd superbracket. -/
theorem chiralGradedCoefficient_eq_superBracket
    (U V : OperatorVector A) :
    chiralGradedCoefficient U V =
      oddOddSuperBracket (sigmaPlus U) (sigmaMinus V) := rfl

end InfoGeometry.Canonical.ChiralSuperconnectionCurvatureBridge
