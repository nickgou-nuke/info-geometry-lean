import InfoGeometry.Optics.LocalGaugeQGTCovariance
import InfoGeometry.OperatorAlgebra.BianchiOperatorLift

/-!
# Local gauge covariance of the adjoint operator derivative

This file supplies the covariant-derivative wire that is deliberately absent
from the algebraic `Connection` owner.  A field carries its value and an
explicit directional derivative channel.  Under a point-dependent right
Maurer--Cartan frame, the derivative of the conjugated field contains the
Leibniz correction `[theta, Ad(field)]`.  This term cancels the inhomogeneous
`-theta` in the transformed connection.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeCovariantDerivative

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent A : Type*} [Ring A]

/-- An operator-valued zero-form together with an explicit directional
derivative.  No manifold calculus is postulated by this carrier. -/
structure AdjointDifferentialField where
  value : Point → A
  derivative : Point → Tangent → A

/-- The adjoint covariant derivative `D_X s = d_X s + [Ω_X,s]`. -/
def adjointCovariantDerivative
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (s : AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) : A :=
  s.derivative p X + associativeCommutator (C.form p X) (s.value p)

/-- Point-dependent conjugation of an adjoint field.  The derivative is the
explicit right Maurer--Cartan Leibniz formula
`d(usu⁻¹) = u(ds)u⁻¹ + [theta,usu⁻¹]`. -/
def localGaugeField
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A)) :
    AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A) where
  value p := innerConjugation (G.frame p) (s.value p)
  derivative p X :=
    innerConjugation (G.frame p) (s.derivative p X) +
      associativeCommutator (G.theta p X)
        (innerConjugation (G.frame p) (s.value p))

@[simp] theorem localGaugeField_value
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) :
    (localGaugeField G s).value p =
      innerConjugation (G.frame p) (s.value p) :=
  rfl

@[simp] theorem localGaugeField_derivative
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    (localGaugeField G s).derivative p X =
      innerConjugation (G.frame p) (s.derivative p X) +
        associativeCommutator (G.theta p X)
          (innerConjugation (G.frame p) (s.value p)) :=
  rfl

/-- The full adjoint covariant derivative is locally gauge covariant.  The
proof uses only the native ring equivalence and associative noncommutative
algebra; it assumes no commutativity of operator coefficients. -/
theorem localGaugeField_covariantDerivative
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (s : AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    adjointCovariantDerivative (localGaugeConnection G C)
        (localGaugeField G s) p X =
      innerConjugation (G.frame p) (adjointCovariantDerivative C s p X) := by
  change
    innerConjugation (G.frame p) (s.derivative p X) +
          associativeCommutator (G.theta p X)
            (innerConjugation (G.frame p) (s.value p)) +
        associativeCommutator
          (innerConjugation (G.frame p) (C.form p X) - G.theta p X)
          (innerConjugation (G.frame p) (s.value p)) =
      innerConjugation (G.frame p)
        (s.derivative p X + associativeCommutator (C.form p X) (s.value p))
  change _ = (innerConjugationRingEquiv (G.frame p))
    (s.derivative p X + associativeCommutator (C.form p X) (s.value p))
  rw [map_add]
  change _ =
    innerConjugation (G.frame p) (s.derivative p X) +
      innerConjugation (G.frame p)
        (C.form p X * s.value p - s.value p * C.form p X)
  have hcomm :
      innerConjugation (G.frame p)
          (C.form p X * s.value p - s.value p * C.form p X) =
        innerConjugation (G.frame p) (C.form p X) *
            innerConjugation (G.frame p) (s.value p) -
          innerConjugation (G.frame p) (s.value p) *
            innerConjugation (G.frame p) (C.form p X) := by
    change (innerConjugationRingEquiv (G.frame p))
        (C.form p X * s.value p - s.value p * C.form p X) =
      (innerConjugationRingEquiv (G.frame p)) (C.form p X) *
          (innerConjugationRingEquiv (G.frame p)) (s.value p) -
        (innerConjugationRingEquiv (G.frame p)) (s.value p) *
          (innerConjugationRingEquiv (G.frame p)) (C.form p X)
    rw [map_sub, map_mul, map_mul]
  rw [hcomm]
  unfold associativeCommutator
  noncomm_ring

/-- Curvature regarded as an adjoint-valued field in two fixed tangent
directions, with its exterior derivative supplied explicitly. -/
def curvatureDifferentialField
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A)
    (U V : Tangent) :
    AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A) where
  value p := curvature C p U V
  derivative p X := dF p X U V

/-- A directional adjoint Bianchi equation for an operator-valued curvature
field.  This is the algebraic interface consumed by differential backends. -/
def SatisfiesAdjointBianchi
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A) : Prop :=
  ∀ p X U V,
    adjointCovariantDerivative C (curvatureDifferentialField C dF U V) p X = 0

/-- Local gauge transformations preserve the adjoint Bianchi equation once
the transformed curvature derivative is the Maurer--Cartan-corrected
derivative of the conjugated curvature field. -/
theorem localGauge_preserves_adjointBianchi
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A)
    (hBianchi : SatisfiesAdjointBianchi C dF)
    (p : Point) (X U V : Tangent) :
    adjointCovariantDerivative (localGaugeConnection G C)
        (localGaugeField G (curvatureDifferentialField C dF U V)) p X = 0 := by
  rw [localGaugeField_covariantDerivative, hBianchi p X U V]
  exact map_zero (innerConjugationRingEquiv (G.frame p))

/-- The transported curvature field has exactly the curvature of the locally
transformed connection as its value. -/
theorem localGauge_curvatureField_value
    (G : RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A)
    (p : Point) (U V : Tangent) :
    (localGaugeField G (curvatureDifferentialField C dF U V)).value p =
      curvature (localGaugeConnection G C) p U V := by
  rw [localGaugeField_value, localGaugeConnection_curvature]
  rfl

end InfoGeometry.Optics.LocalGaugeCovariantDerivative
