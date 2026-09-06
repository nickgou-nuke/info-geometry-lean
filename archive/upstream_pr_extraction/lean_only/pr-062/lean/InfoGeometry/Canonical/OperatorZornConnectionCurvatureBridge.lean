import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Operator-Zorn curvature readout

This owner identifies the ordered operator cross product with the Hodge readout
of the curvature of a constant operator-valued connection.  It introduces no
manifold, Dirac operator, or gauge-field interpretation: the statement is the
finite connection/commutator bridge supplied by the existing owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge

open InfoGeometry.Canonical
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Optics.OperatorValuedConnection

variable {A : Type*} [Ring A]

def operatorVectorForm (U : OperatorVector A) :
    OperatorOneForm Unit (Fin 3) A :=
  fun _ i => U i

def constantOperatorConnection (U : OperatorVector A) :
    Connection (Point := Unit) (Tangent := Fin 3) (Value := A) where
  form := operatorVectorForm U
  derivative := fun _ _ _ => 0
  derivative_swap := by intro; simp
  derivative_same := by intro; simp

theorem constantConnection_curvature_eq_wedge
    (U : OperatorVector A) (i j : Fin 3) :
    curvature (constantOperatorConnection U) () i j =
      operatorWedge2 U U i j := by
  simp [curvature, constantOperatorConnection, operatorVectorForm,
    wedgeSquare, operatorWedge2]

theorem constantConnection_curvature_hodge_eq_operatorCross
    (U : OperatorVector A) :
    operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection U) () i j) =
      operatorCross U U := by
  rw [show (fun i j => curvature (constantOperatorConnection U) () i j) =
      operatorWedge2 U U by
        funext i j
        exact constantConnection_curvature_eq_wedge U i j]
  exact operatorHodgeDual2_wedge_eq_operatorCross U U

theorem constantConnection_curvature_hodge_component_commutators
    (U : OperatorVector A) :
    (operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection U) () i j)) 0 =
      U 1 * U 2 - U 2 * U 1 ∧
    (operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection U) () i j)) 1 =
      U 2 * U 0 - U 0 * U 2 ∧
    (operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection U) () i j)) 2 =
      U 0 * U 1 - U 1 * U 0 := by
  rw [constantConnection_curvature_hodge_eq_operatorCross]
  exact ⟨rfl, rfl, rfl⟩

def operatorZornMetricPart (U V : OperatorVector A) : OperatorZornMatrix A :=
  operatorZornCoordinates (operatorDot U V) (operatorDot V U) 0 0

def operatorZornCurvaturePart (U V : OperatorVector A) : OperatorZornMatrix A :=
  operatorZornCoordinates
    0 0
    (-(operatorHodgeDual2
      (fun i j => curvature (constantOperatorConnection V) () i j)))
    (operatorHodgeDual2
      (fun i j => curvature (constantOperatorConnection U) () i j))

theorem chiralOperatorZorn_square_eq_metric_add_curvature
    (U V : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn U V) (chiralOperatorZorn U V) =
      operatorZornMetricPart U V + operatorZornCurvaturePart U V := by
  rw [operatorZornMul_chiralOperatorZorn_hodge]
  have hU := constantConnection_curvature_hodge_eq_operatorCross U
  have hV := constantConnection_curvature_hodge_eq_operatorCross V
  apply operatorZornMatrix_ext
  · change operatorDot U V = operatorDot U V + 0
    simp
  · change operatorDot V U = operatorDot V U + 0
    simp
  · change -(operatorHodgeDual2 (operatorWedge2 V V)) =
      0 + -(operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection V) () i j))
    rw [operatorHodgeDual2_wedge_eq_operatorCross, hV]
    simp
  · change operatorHodgeDual2 (operatorWedge2 U U) =
      0 + operatorHodgeDual2
        (fun i j => curvature (constantOperatorConnection U) () i j)
    rw [operatorHodgeDual2_wedge_eq_operatorCross, hU]
    simp

theorem chiralOperatorZorn_square_curvature_readout
    (U V : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn U V) (chiralOperatorZorn U V) =
      operatorZornCoordinates
        (operatorDot U V)
        (operatorDot V U)
        (-(operatorHodgeDual2
          (fun i j => curvature (constantOperatorConnection V) () i j)))
        (operatorHodgeDual2
          (fun i j => curvature (constantOperatorConnection U) () i j)) := by
  have hU : (fun i j => curvature (constantOperatorConnection U) () i j) =
      operatorWedge2 U U := by
    funext i j
    exact constantConnection_curvature_eq_wedge U i j
  have hV : (fun i j => curvature (constantOperatorConnection V) () i j) =
      operatorWedge2 V V := by
    funext i j
    exact constantConnection_curvature_eq_wedge V i j
  rw [hU, hV]
  exact operatorZornMul_chiralOperatorZorn_hodge U V

end InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge
