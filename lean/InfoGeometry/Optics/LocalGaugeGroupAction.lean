import InfoGeometry.Optics.LocalGaugeFrameInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native group action of local operator gauge frames

This file packages the previously proved semidirect frame laws as a native
Mathlib `Group` and upgrades pointwise form/curvature composition to equality
of complete connection structures.  Local gauge transformation is therefore
a genuine `MulAction` on the operator-valued connection carrier.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeGroupAction

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeFrameComposition
open InfoGeometry.Optics.LocalGaugeFrameInverse
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent A : Type*} [Ring A]

/-- A separate carrier for right Maurer--Cartan frames equipped with their
semidirect group structure. -/
def RightGaugeGroup :=
  RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A)

instance : Mul (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) :=
  ⟨composeRightFrames⟩

instance : One (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) :=
  ⟨identityRightFrame⟩

instance : Inv (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) :=
  ⟨inverseRightFrame⟩

instance : Group (RightGaugeGroup
    (Point := Point) (Tangent := Tangent) (A := A)) :=
  Group.ofLeftAxioms
    (fun K H G => (composeRightFrames_assoc K H G).symm)
    identityRightFrame_compose
    inverseRightFrame_compose

@[simp] theorem rightGaugeGroup_mul_def
    (H G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) :
    H * G = composeRightFrames H G :=
  rfl

@[simp] theorem rightGaugeGroup_one_def :
    (1 : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) =
      identityRightFrame :=
  rfl

@[simp] theorem rightGaugeGroup_inv_def
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) :
    G⁻¹ = inverseRightFrame G :=
  rfl

/-- Extensionality for the algebraic connection owner.  Proof fields are
irrelevant once the form and derivative data agree. -/
theorem connection_ext
    {C D : Connection (Point := Point) (Tangent := Tangent) (Value := A)}
    (hform : C.form = D.form)
    (hderivative : C.derivative = D.derivative) : C = D := by
  cases C with
  | mk formC derivativeC swapC sameC =>
    cases D with
    | mk formD derivativeD swapD sameD =>
      cases hform
      cases hderivative
      rfl

/-- Equality of connection forms and curvature determines equality of the
stored exterior derivative channel. -/
theorem connection_derivative_eq_of_form_curvature_eq
    {C D : Connection (Point := Point) (Tangent := Tangent) (Value := A)}
    (hform : C.form = D.form)
    (hcurvature : ∀ p X Y, curvature C p X Y = curvature D p X Y) :
    C.derivative = D.derivative := by
  funext p X Y
  have h := hcurvature p X Y
  unfold curvature at h
  rw [hform] at h
  exact add_right_cancel h

/-- Successive local transformations equal transformation by the product
frame as complete connection structures, not merely pointwise readouts. -/
theorem localGaugeConnection_mul
    (H G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    localGaugeConnection (H * G) C =
      localGaugeConnection H (localGaugeConnection G C) := by
  apply connection_ext
  · funext p X
    exact (localGaugeConnection_compose_form H G C p X).symm
  · apply connection_derivative_eq_of_form_curvature_eq
    · funext p X
      exact (localGaugeConnection_compose_form H G C p X).symm
    · intro p X Y
      exact (localGaugeConnection_compose_curvature H G C p X Y).symm

/-- The identity gauge frame fixes the complete connection structure. -/
@[simp] theorem localGaugeConnection_one
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    localGaugeConnection
        (1 : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) C = C := by
  apply connection_ext
  · funext p X
    exact identityRightFrame_connection_form C p X
  · apply connection_derivative_eq_of_form_curvature_eq
    · funext p X
      exact identityRightFrame_connection_form C p X
    · exact identityRightFrame_connection_curvature C

/-- Native action of the local right gauge group on complete operator-valued
connections. -/
instance : SMul
    (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (Connection (Point := Point) (Tangent := Tangent) (Value := A)) where
  smul G C := localGaugeConnection G C

instance : MulAction
    (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (Connection (Point := Point) (Tangent := Tangent) (Value := A)) where
  one_smul := localGaugeConnection_one
  mul_smul := localGaugeConnection_mul

@[simp] theorem rightGaugeGroup_smul_form
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X : Tangent) :
    (G • C).form p X =
      innerConjugation (G.frame p) (C.form p X) - G.theta p X :=
  rfl

@[simp] theorem rightGaugeGroup_smul_curvature
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (G • C) p X Y =
      innerConjugation (G.frame p) (curvature C p X Y) :=
  localGaugeConnection_curvature G C p X Y

/-- The inverse group element recovers the original complete connection. -/
@[simp] theorem inv_smul_smul_connection
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
  (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    G⁻¹ • G • C = C := by
  rw [← mul_smul, Group.inv_mul_cancel, one_smul]

end InfoGeometry.Optics.LocalGaugeGroupAction
