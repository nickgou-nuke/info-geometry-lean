import InfoGeometry.Optics.LocalGaugeCovariantDerivative

/-!
# Composition laws for local operator gauge frames

For the right Maurer--Cartan convention, successive transformations by `G`
and then `H` use the product frame `H.frame * G.frame` and the semidirect
one-form

`theta_H + Ad(H.frame) theta_G`.

This file proves the identity and associativity laws and verifies that this
composition acts correctly on connection forms, curvature, and adjoint
fields.  All statements hold in an arbitrary associative ring.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeFrameComposition

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent A : Type*} [Ring A]

/-- Inner conjugation by a product is successive inner conjugation, with the
left factor acting last. -/
theorem innerConjugation_mul (u v : Aˣ) (a : A) :
    innerConjugation (u * v) a =
      innerConjugation u (innerConjugation v a) := by
  simp [innerConjugation, mul_assoc]

@[simp] theorem innerConjugation_one (a : A) :
    innerConjugation (1 : Aˣ) a = a := by
  simp [innerConjugation]

@[simp] theorem innerConjugation_zero (u : Aˣ) :
    innerConjugation u (0 : A) = 0 := by
  change (innerConjugationRingEquiv u) 0 = 0
  exact map_zero (innerConjugationRingEquiv u)

/-- Identity right Maurer--Cartan frame. -/
def identityRightFrame :
    RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A) where
  frame := fun _ => 1
  theta := fun _ _ => 0

/-- Semidirect composition of right Maurer--Cartan frames.  `compose H G`
represents first applying `G` and then applying `H`. -/
def composeRightFrames
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A) where
  frame p := H.frame p * G.frame p
  theta p X := H.theta p X +
    innerConjugation (H.frame p) (G.theta p X)

@[simp] theorem composeRightFrames_frame
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (composeRightFrames H G).frame p = H.frame p * G.frame p :=
  rfl

@[simp] theorem composeRightFrames_theta
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    (composeRightFrames H G).theta p X =
      H.theta p X + innerConjugation (H.frame p) (G.theta p X) :=
  rfl

/-- The right-frame composition is associative. -/
theorem composeRightFrames_assoc
    (K H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    composeRightFrames K (composeRightFrames H G) =
      composeRightFrames (composeRightFrames K H) G := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp only [composeRightFrames_frame]
    exact (mul_assoc (K.frame p) (H.frame p) (G.frame p)).symm
  · funext p X
    change K.theta p X +
          innerConjugation (K.frame p)
            (H.theta p X + innerConjugation (H.frame p) (G.theta p X)) =
        (K.theta p X + innerConjugation (K.frame p) (H.theta p X)) +
          innerConjugation (K.frame p * H.frame p) (G.theta p X)
    change K.theta p X +
          (innerConjugationRingEquiv (K.frame p))
            (H.theta p X + innerConjugation (H.frame p) (G.theta p X)) = _
    rw [map_add, innerConjugationRingEquiv_apply,
      innerConjugationRingEquiv_apply, innerConjugation_mul]
    exact (add_assoc _ _ _).symm

@[simp] theorem identityRightFrame_compose
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    composeRightFrames identityRightFrame G = G := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp [identityRightFrame]
  · funext p X
    simp [identityRightFrame]

@[simp] theorem compose_identityRightFrame
    (G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A)) :
    composeRightFrames G identityRightFrame = G := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    simp [identityRightFrame]
  · funext p X
    simp [identityRightFrame]

/-- Successive local transformations have the same connection one-form as
the semidirectly composed right frame. -/
theorem localGaugeConnection_compose_form
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (localGaugeConnection H (localGaugeConnection G C)).form p X =
      (localGaugeConnection (composeRightFrames H G) C).form p X := by
  rw [localGaugeConnection_form, localGaugeConnection_form,
    localGaugeConnection_form]
  simp only [composeRightFrames_frame, composeRightFrames_theta]
  rw [innerConjugation_mul]
  change (innerConjugationRingEquiv (H.frame p))
        (innerConjugation (G.frame p) (C.form p X) - G.theta p X) -
      H.theta p X = _
  rw [map_sub, innerConjugationRingEquiv_apply,
    innerConjugationRingEquiv_apply]
  noncomm_ring

/-- Successive local gauge transformations and the semidirectly composed
frame have identical full curvature. -/
theorem localGaugeConnection_compose_curvature
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (localGaugeConnection H (localGaugeConnection G C)) p X Y =
      curvature (localGaugeConnection (composeRightFrames H G) C) p X Y := by
  rw [localGaugeConnection_curvature, localGaugeConnection_curvature,
    localGaugeConnection_curvature]
  exact (innerConjugation_mul (H.frame p) (G.frame p)
    (curvature C p X Y)).symm

/-- The identity right frame acts trivially on connection forms. -/
@[simp] theorem identityRightFrame_connection_form
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (localGaugeConnection identityRightFrame C).form p X = C.form p X := by
  simp [localGaugeConnection_form, identityRightFrame, innerConjugation]

/-- The identity right frame acts trivially on curvature. -/
@[simp] theorem identityRightFrame_connection_curvature
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (localGaugeConnection identityRightFrame C) p X Y =
      curvature C p X Y := by
  rw [localGaugeConnection_curvature]
  exact innerConjugation_one (curvature C p X Y)

/-- Adjoint fields compose under the same pointwise product frame. -/
theorem localGaugeField_compose_value
    (H G : RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (localGaugeField H (localGaugeField G s)).value p =
      (localGaugeField (composeRightFrames H G) s).value p := by
  simp only [localGaugeField_value, composeRightFrames_frame]
  exact (innerConjugation_mul (H.frame p) (G.frame p) (s.value p)).symm

end InfoGeometry.Optics.LocalGaugeFrameComposition
