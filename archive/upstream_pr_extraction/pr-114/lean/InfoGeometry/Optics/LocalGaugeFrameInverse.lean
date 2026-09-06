import InfoGeometry.Optics.LocalGaugeFrameComposition

/-!
# Inverses of local operator gauge frames

The inverse of a right Maurer--Cartan frame `(u, theta)` is
`(u⁻¹, -Ad(u⁻¹) theta)`.  Together with the semidirect composition owner this
completes the group laws and proves reversibility of local operator transport.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeFrameInverse

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.LocalGaugeFrameComposition
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent A : Type*} [Ring A]

/-- Conjugation by a unit and then its inverse is the identity. -/
@[simp] theorem innerConjugation_inv_apply (u : Aˣ) (a : A) :
    innerConjugation (u⁻¹) (innerConjugation u a) = a := by
  simp [innerConjugation, mul_assoc]

/-- Conjugation by the inverse and then the unit is the identity. -/
@[simp] theorem innerConjugation_apply_inv (u : Aˣ) (a : A) :
    innerConjugation u (innerConjugation (u⁻¹) a) = a := by
  simp [innerConjugation, mul_assoc]

@[simp] theorem innerConjugation_neg (u : Aˣ) (a : A) :
    innerConjugation u (-a) = -innerConjugation u a := by
  change (innerConjugationRingEquiv u) (-a) =
    -(innerConjugationRingEquiv u) a
  exact map_neg (innerConjugationRingEquiv u) a

/-- Inverse right Maurer--Cartan frame. -/
def inverseRightFrame
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A) where
  frame p := (G.frame p)⁻¹
  theta p X := -innerConjugation (G.frame p)⁻¹ (G.theta p X)

@[simp] theorem inverseRightFrame_frame
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (inverseRightFrame G).frame p = (G.frame p)⁻¹ :=
  rfl

@[simp] theorem inverseRightFrame_theta
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    (inverseRightFrame G).theta p X =
      -innerConjugation (G.frame p)⁻¹ (G.theta p X) :=
  rfl

/-- The inverse frame composed after a frame is the identity. -/
@[simp] theorem inverseRightFrame_compose
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    composeRightFrames (inverseRightFrame G) G = identityRightFrame := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp
  · funext p X
    simp

/-- A frame composed after its inverse is the identity. -/
@[simp] theorem compose_inverseRightFrame
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    composeRightFrames G (inverseRightFrame G) = identityRightFrame := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp
  · funext p X
    simp

/-- Taking the inverse frame twice recovers the original frame. -/
@[simp] theorem inverseRightFrame_involutive
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    inverseRightFrame (inverseRightFrame G) = G := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp
  · funext p X
    simp

/-- Applying a frame and then its inverse recovers the connection one-form. -/
theorem inverse_localGaugeConnection_form
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (localGaugeConnection (inverseRightFrame G)
        (localGaugeConnection G C)).form p X = C.form p X := by
  rw [localGaugeConnection_compose_form, inverseRightFrame_compose,
    identityRightFrame_connection_form]

/-- Applying the inverse and then the original frame also recovers the
connection one-form. -/
theorem localGaugeConnection_inverse_form
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (localGaugeConnection G
        (localGaugeConnection (inverseRightFrame G) C)).form p X = C.form p X := by
  rw [localGaugeConnection_compose_form, compose_inverseRightFrame,
    identityRightFrame_connection_form]

/-- Applying a frame and then its inverse recovers the full curvature. -/
theorem inverse_localGaugeConnection_curvature
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature
        (localGaugeConnection (inverseRightFrame G)
          (localGaugeConnection G C)) p X Y = curvature C p X Y := by
  rw [localGaugeConnection_compose_curvature, inverseRightFrame_compose,
    identityRightFrame_connection_curvature]

/-- Applying the inverse and then the original frame also recovers the full
curvature. -/
theorem localGaugeConnection_inverse_curvature
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature
        (localGaugeConnection G
          (localGaugeConnection (inverseRightFrame G) C)) p X Y =
      curvature C p X Y := by
  rw [localGaugeConnection_compose_curvature, compose_inverseRightFrame,
    identityRightFrame_connection_curvature]

/-- Applying a frame and then its inverse recovers every adjoint field value. -/
theorem inverse_localGaugeField_value
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (localGaugeField (inverseRightFrame G) (localGaugeField G s)).value p =
      s.value p := by
  simp

/-- Applying the inverse and then the original frame recovers every adjoint
field value. -/
theorem localGaugeField_inverse_value
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (localGaugeField G (localGaugeField (inverseRightFrame G) s)).value p =
      s.value p := by
  simp

end InfoGeometry.Optics.LocalGaugeFrameInverse
