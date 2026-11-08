import InfoGeometry.Lie.CanonicalZornDerivationLane
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.DerivationVectorCalculus

/-!
# Finite vector calculus on the canonical Zorn derivation lane

This module is only the concrete specialization of the general three-direction
calculus.  A frame is supplied by the caller; no preferred spatial basis is
chosen implicitly.
-/

namespace InfoGeometry.Lie.CanonicalZornFiniteVectorCalculus

open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.OperatorAlgebra.DerivationVectorCalculus

abbrev ZornFrame3 :=
  DerivationFrame3 canonicalZornDerivationLane

abbrev ZornVector3 :=
  Vector3 (A := ZornCarrier)

/-- The oriented three-dimensional Levi--Civita symbol. -/
def leviCivita3 (i j k : Fin 3) : ℝ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨
      (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨
      (i, j, k) = (1, 0, 2) then -1
  else 0

noncomputable def gradient (frame : ZornFrame3) (X : ZornCarrier) : ZornVector3 :=
  InfoGeometry.OperatorAlgebra.DerivationVectorCalculus.gradient
    canonicalZornDerivationLane frame X

noncomputable def curl (frame : ZornFrame3) (v : ZornVector3) : ZornVector3 :=
  InfoGeometry.OperatorAlgebra.DerivationVectorCalculus.curl
    canonicalZornDerivationLane frame v

def FrameCommutes (frame : ZornFrame3) : Prop :=
  InfoGeometry.OperatorAlgebra.DerivationVectorCalculus.FrameCommutes
    canonicalZornDerivationLane frame

theorem curl_gradient_eq_bracketAction
    (frame : ZornFrame3) (X : ZornCarrier) :
    curl frame (gradient frame X) =
      fun i =>
        if i = (0 : Fin 3) then
          canonicalZornDerivationLane.operatorAction ⁅frame 1, frame 2⁆ X
        else if i = (1 : Fin 3) then
          canonicalZornDerivationLane.operatorAction ⁅frame 2, frame 0⁆ X
        else
          canonicalZornDerivationLane.operatorAction ⁅frame 0, frame 1⁆ X := by
  exact InfoGeometry.OperatorAlgebra.DerivationVectorCalculus.curl_gradient_eq_bracketAction
    canonicalZornDerivationLane frame X

theorem curl_gradient_eq_zero_of_commute
    (frame : ZornFrame3) (hframe : FrameCommutes frame) (X : ZornCarrier) :
    curl frame (gradient frame X) = fun _ => 0 := by
  exact InfoGeometry.OperatorAlgebra.DerivationVectorCalculus.curl_gradient_eq_zero_of_commute
    canonicalZornDerivationLane frame hframe X

end InfoGeometry.Lie.CanonicalZornFiniteVectorCalculus
