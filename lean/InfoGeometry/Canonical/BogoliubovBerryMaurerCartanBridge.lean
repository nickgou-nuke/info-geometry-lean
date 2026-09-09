import InfoGeometry.NCG.NoncommutativeConnectionCurvature
import InfoGeometry.Optics.LocalGaugeCovariantDerivative
import InfoGeometry.Krein.HessianFrameConjugation

/-!
# Bogoliubov/Berry Maurer--Cartan bridge

This file isolates the theorem-safe algebraic content of the ``dressed vacuum''
picture.  A frame is an invertible algebra element and its connection is the
right Maurer--Cartan expression already owned by
`InfoGeometry.NCG.NoncommutativeConnectionCurvature`.  A central affine shift
is kept as a separate datum: it changes a scalar reference, but not an
associative commutator.

No smooth manifold, vielbein, Levi--Civita connection, or equality between a
Berry connection and a gravitational spin connection is asserted here.  Those
require additional differentiable geometric data.  The file therefore closes
the algebraic causal cone and leaves that analytic identification explicit.
-/

noncomputable section

namespace InfoGeometry.Canonical.BogoliubovBerryMaurerCartanBridge

open InfoGeometry.NCG
open InfoGeometry.OperatorAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-! ## Affine central shifts -/

/-- An affine operator shift whose added term is central in the coefficient algebra. -/
structure CentralAffineShift where
  linear : A
  offset : A
  central_offset : ∀ x : A, offset * x = x * offset

/-- The affine action on an observable. -/
def CentralAffineShift.apply (B : CentralAffineShift (A := A)) (x : A) : A :=
  B.linear * x - x * B.linear + (B.offset * x - x * B.offset)

theorem CentralAffineShift.apply_eq_commutator
    (B : CentralAffineShift (A := A)) (x : A) :
    B.apply x = B.linear * x - x * B.linear := by
  unfold CentralAffineShift.apply
  rw [B.central_offset x]
  simp

theorem CentralAffineShift.apply_additive_offset
    (B : CentralAffineShift (A := A)) (x : A) :
    (B.linear + B.offset) * x - x * (B.linear + B.offset) = B.apply x := by
  unfold CentralAffineShift.apply
  simp only [add_mul, mul_add]
  abel

/-! ## Pure-gauge Maurer--Cartan flatness -/

/-- The right Maurer--Cartan coefficient attached to an algebraic frame. -/
def berryMaurerCartan
    (D : AlgebraDerivation R A) (u : Aˣ) : A :=
  AlgebraDerivation.pureGaugeForm D u

/-- The intrinsic flatness equation for the dressed-vacuum/Berry frame. -/
theorem berryMaurerCartan_flat
    (D : AlgebraDerivation R A) (u : Aˣ) :
    D (u : A) * D (u⁻¹ : Aˣ).val +
        berryMaurerCartan D u * berryMaurerCartan D u = 0 := by
  exact AlgebraDerivation.maurer_cartan_flatness D u

/-- The affine shift and the Maurer--Cartan curvature equation are independent
    layers: adding a central offset preserves the commutator while the frame
    contribution obeys its own flatness identity. -/
theorem affine_shift_and_berry_flatness
    (B : CentralAffineShift (A := A))
    (D : AlgebraDerivation R A) (u : Aˣ) (x : A) :
    B.apply x = B.linear * x - x * B.linear ∧
      D (u : A) * D (u⁻¹ : Aˣ).val +
          berryMaurerCartan D u * berryMaurerCartan D u = 0 := by
  exact ⟨B.apply_eq_commutator x, berryMaurerCartan_flat D u⟩

/-! ## Operator-valued local gauge transport -/

variable {Point Tangent : Type*}

/-- The existing local-gauge owner transports an adjoint field covariantly.
    This is the operator-algebraic Berry-frame statement: the derivative
    correction is exactly the Maurer--Cartan term. -/
theorem berry_frame_covariant_transport
    (G : InfoGeometry.Optics.LocalGaugeQGTCovariance.RightMaurerCartanFrame
      (Point := Point) (Tangent := Tangent) (A := A))
    (C : InfoGeometry.Optics.OperatorValuedConnection.Connection
      (Point := Point) (Tangent := Tangent) (Value := A))
    (s : InfoGeometry.Optics.LocalGaugeCovariantDerivative.AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    InfoGeometry.Optics.LocalGaugeCovariantDerivative.adjointCovariantDerivative
        (InfoGeometry.Optics.LocalGaugeQGTCovariance.localGaugeConnection G C)
        (InfoGeometry.Optics.LocalGaugeCovariantDerivative.localGaugeField G s) p X =
      innerConjugation
        (G.frame p)
        (InfoGeometry.Optics.LocalGaugeCovariantDerivative.adjointCovariantDerivative C s p X) := by
  exact InfoGeometry.Optics.LocalGaugeCovariantDerivative.localGaugeField_covariantDerivative
    G C s p X

end InfoGeometry.Canonical.BogoliubovBerryMaurerCartanBridge

end
