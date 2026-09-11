import InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Representation channels for operator-Zorn curvature

This owner records the honest representation boundary between the native
operator-valued Zorn calculus and a target coefficient algebra.  A ring
homomorphism transports the ordered dot/cross channels, the Zorn square, and
the constant-connection curvature readout.  No Dirac or Lichnerowicz claim is
made until a concrete map into a Dirac endomorphism carrier is supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge

open InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Physics.NCG

variable {A B : Type*} [Ring A] [Ring B]

def mapOperatorVector (ρ : A →+* B) (U : OperatorVector A) : OperatorVector B :=
  fun i => ρ (U i)

theorem mapOperatorVector_dot (ρ : A →+* B)
    (U V : OperatorVector A) :
    ρ (operatorDot U V) =
      operatorDot (mapOperatorVector ρ U) (mapOperatorVector ρ V) := by
  simp [operatorDot, mapOperatorVector, NCZornElement.zornDot]

theorem mapOperatorVector_cross (ρ : A →+* B)
    (U V : OperatorVector A) :
    mapOperatorVector ρ (operatorCross U V) =
      operatorCross (mapOperatorVector ρ U) (mapOperatorVector ρ V) := by
  funext i
  fin_cases i <;>
    simp [mapOperatorVector, operatorCross, NCZornElement.zornCross]

theorem mapOperatorVector_wedge2 (ρ : A →+* B)
    (U V : OperatorVector A) :
    (fun i j => ρ (operatorWedge2 U V i j)) =
      operatorWedge2 (mapOperatorVector ρ U) (mapOperatorVector ρ V) := by
  funext i j
  simp [operatorWedge2, mapOperatorVector]

theorem mapOperatorVector_hodgeDual2 (ρ : A →+* B)
    (K : Fin 3 → Fin 3 → A) :
    mapOperatorVector ρ (operatorHodgeDual2 K) =
      operatorHodgeDual2 (fun i j => ρ (K i j)) := by
  funext i
  fin_cases i <;> rfl

theorem mapOperatorVector_neg (ρ : A →+* B) (U : OperatorVector A) :
    mapOperatorVector ρ (-U) = -(mapOperatorVector ρ U) := by
  funext i
  simp [mapOperatorVector]

theorem mapOperatorVector_chiralSquare (ρ : A →+* B)
    (U V : OperatorVector A) :
    operatorZornCoordinates (ρ (operatorDot U V)) (ρ (operatorDot V U))
          (mapOperatorVector ρ (-operatorCross V V))
          (mapOperatorVector ρ (operatorCross U U)) =
      operatorZornCoordinates
        (operatorDot (mapOperatorVector ρ U) (mapOperatorVector ρ V))
        (operatorDot (mapOperatorVector ρ V) (mapOperatorVector ρ U))
        (-operatorCross (mapOperatorVector ρ V) (mapOperatorVector ρ V))
        (operatorCross (mapOperatorVector ρ U) (mapOperatorVector ρ U)) := by
  apply operatorZornMatrix_ext
  · change ρ (operatorDot U V) =
      operatorDot (mapOperatorVector ρ U) (mapOperatorVector ρ V)
    exact mapOperatorVector_dot ρ U V
  · change ρ (operatorDot V U) =
      operatorDot (mapOperatorVector ρ V) (mapOperatorVector ρ U)
    exact mapOperatorVector_dot ρ V U
  · change mapOperatorVector ρ (-operatorCross V V) =
      -operatorCross (mapOperatorVector ρ V) (mapOperatorVector ρ V)
    calc
      mapOperatorVector ρ (-operatorCross V V) =
          -(mapOperatorVector ρ (operatorCross V V)) :=
        mapOperatorVector_neg ρ (operatorCross V V)
      _ = -operatorCross (mapOperatorVector ρ V) (mapOperatorVector ρ V) :=
        congrArg Neg.neg (mapOperatorVector_cross ρ V V)
  · change mapOperatorVector ρ (operatorCross U U) =
      operatorCross (mapOperatorVector ρ U) (mapOperatorVector ρ U)
    exact mapOperatorVector_cross ρ U U

theorem mapConstantConnection_curvature (ρ : A →+* B)
    (U : OperatorVector A) (i j : Fin 3) :
    ρ (curvature (constantOperatorConnection U) () i j) =
      curvature (constantOperatorConnection (mapOperatorVector ρ U)) () i j := by
  rw [constantConnection_curvature_eq_wedge,
    constantConnection_curvature_eq_wedge]
  have h := mapOperatorVector_wedge2 ρ U U
  have hi := congrFun h i
  have hij := congrFun hi j
  exact hij

end InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge
