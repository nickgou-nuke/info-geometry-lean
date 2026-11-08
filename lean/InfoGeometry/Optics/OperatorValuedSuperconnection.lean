import InfoGeometry.Optics.OperatorValuedConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SupergradedCuntzBdG
import InfoGeometry.Algebra.SupergradedJordanLieSplit

noncomputable section

/-!
# Graded operator-valued connection curvature

This is the minimal graded completion of `OperatorValuedConnection`.  The
coefficient algebra remains associative; only the Koszul parity sign changes
the mixed product.  No Zorn subtraction or new Clifford multiplication is
introduced here.
-/

namespace InfoGeometry.Optics.OperatorValuedConnection

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Physics.SupergradedCuntzBdG

variable {Point Tangent Value : Type*} [Ring Value]

/-- The parity-sensitive coefficient wedge square. -/
def gradedWedgeSquare
    (ω : OperatorOneForm Point Tangent Value)
    (parity : Point → Tangent → Z2Parity)
    (p : Point) (X Y : Tangent) : Value :=
  match parity p X, parity p Y with
  | Z2Parity.odd, Z2Parity.odd => ω p X * ω p Y + ω p Y * ω p X
  | _, _ => ω p X * ω p Y - ω p Y * ω p X

/-- A connection together with the internal parity of each coefficient. -/
structure SuperConnection where
  form : OperatorOneForm Point Tangent Value
  derivative : Point → Tangent → Tangent → Value
  derivative_swap : ∀ p X Y, derivative p Y X = -derivative p X Y
  derivative_same : ∀ p X, derivative p X X = 0
  parity : Point → Tangent → Z2Parity

/-- Graded curvature `dΩ + Ω ∧ₛ Ω`. -/
def superconnectionCurvature (C : SuperConnection (Point := Point)
    (Tangent := Tangent) (Value := Value)) (p : Point) (X Y : Tangent) : Value :=
  C.derivative p X Y + gradedWedgeSquare C.form C.parity p X Y

theorem gradedWedgeSquare_even_even_eq_wedgeSquare
    (ω : OperatorOneForm Point Tangent Value)
    (parity : Point → Tangent → Z2Parity)
    (p : Point) (X Y : Tangent)
    (hX : parity p X = Z2Parity.even)
    (hY : parity p Y = Z2Parity.even) :
    gradedWedgeSquare ω parity p X Y = wedgeSquare ω p X Y := by
  simp [gradedWedgeSquare, hX, hY, wedgeSquare]

theorem gradedWedgeSquare_odd_odd_eq_anticommutator
    (ω : OperatorOneForm Point Tangent Value)
    (parity : Point → Tangent → Z2Parity)
    (p : Point) (X Y : Tangent)
    (hX : parity p X = Z2Parity.odd)
    (hY : parity p Y = Z2Parity.odd) :
    gradedWedgeSquare ω parity p X Y =
      ω p X * ω p Y + ω p Y * ω p X := by
  simp [gradedWedgeSquare, hX, hY]

theorem superconnectionCurvature_even_eq_curvature
    (C : SuperConnection (Point := Point) (Tangent := Tangent) (Value := Value))
    (hEven : ∀ p X, C.parity p X = Z2Parity.even)
    (p : Point) (X Y : Tangent) :
    superconnectionCurvature C p X Y =
      curvature
        { form := C.form
          derivative := C.derivative
          derivative_swap := C.derivative_swap
          derivative_same := C.derivative_same } p X Y := by
  unfold superconnectionCurvature curvature
  rw [gradedWedgeSquare_even_even_eq_wedgeSquare C.form C.parity p X Y
      (hEven p X) (hEven p Y)]

theorem superconnectionCurvature_odd_odd
    (C : SuperConnection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y : Tangent)
    (hX : C.parity p X = Z2Parity.odd)
    (hY : C.parity p Y = Z2Parity.odd) :
    superconnectionCurvature C p X Y =
      C.derivative p X Y + C.form p X * C.form p Y + C.form p Y * C.form p X := by
  unfold superconnectionCurvature
  rw [gradedWedgeSquare_odd_odd_eq_anticommutator C.form C.parity p X Y hX hY]
  rw [add_assoc]

/-- Inner transport by an even invertible coefficient. -/
def innerTransport (U Uinv A : Value) : Value := U * A * Uinv

theorem innerTransport_mul
    (U Uinv A B : Value)
    (hRight : Uinv * U = 1) :
    innerTransport U Uinv (A * B) =
      innerTransport U Uinv A * innerTransport U Uinv B := by
  unfold innerTransport
  calc
    U * (A * B) * Uinv = U * A * B * Uinv := by simp [mul_assoc]
    _ = U * A * (Uinv * U) * B * Uinv := by
      rw [hRight]
      simp [mul_assoc]
    _ = (U * A * Uinv) * (U * B * Uinv) := by
      rw [hRight]
      simp only [mul_one, mul_assoc]
      rw [← mul_assoc Uinv U (B * Uinv), hRight, one_mul]

theorem innerTransport_add
    (U Uinv A B : Value) :
    innerTransport U Uinv (A + B) =
      innerTransport U Uinv A + innerTransport U Uinv B := by
  unfold innerTransport
  simp only [add_mul, mul_add]

theorem innerTransport_sub
    (U Uinv A B : Value) :
    innerTransport U Uinv (A - B) =
      innerTransport U Uinv A - innerTransport U Uinv B := by
  unfold innerTransport
  simp only [sub_mul, mul_sub]

theorem innerTransport_gradedWedgeSquare
    (ω : OperatorOneForm Point Tangent Value)
    (parity : Point → Tangent → Z2Parity)
    (U Uinv : Value) (p : Point) (X Y : Tangent)
    (hRight : Uinv * U = 1) :
    gradedWedgeSquare
        (fun p X => innerTransport U Uinv (ω p X)) parity p X Y =
      innerTransport U Uinv (gradedWedgeSquare ω parity p X Y) := by
  unfold gradedWedgeSquare
  cases hX : parity p X <;> cases hY : parity p Y
  · rw [innerTransport_sub, innerTransport_mul U Uinv _ _ hRight,
      innerTransport_mul U Uinv _ _ hRight]
  · rw [innerTransport_sub, innerTransport_mul U Uinv _ _ hRight,
      innerTransport_mul U Uinv _ _ hRight]
  · rw [innerTransport_sub, innerTransport_mul U Uinv _ _ hRight,
      innerTransport_mul U Uinv _ _ hRight]
  · rw [innerTransport_add, innerTransport_mul U Uinv _ _ hRight,
      innerTransport_mul U Uinv _ _ hRight]

/--
Curvature covariance once both the connection form and its derivative have
been supplied as transported data.  The derivative hypothesis is explicit:
this theorem does not infer covariance of an arbitrary differential operator.
-/
theorem superconnectionCurvature_innerTransport
    (C C' : SuperConnection (Point := Point) (Tangent := Tangent)
      (Value := Value))
    (U Uinv : Value) (p : Point) (X Y : Tangent)
    (hRight : Uinv * U = 1)
    (hForm : ∀ p X, C'.form p X = innerTransport U Uinv (C.form p X))
    (hDerivative : ∀ p X Y,
      C'.derivative p X Y = innerTransport U Uinv (C.derivative p X Y))
    (hParity : C'.parity = C.parity) :
    superconnectionCurvature C' p X Y =
      innerTransport U Uinv (superconnectionCurvature C p X Y) := by
  have hFormEq : C'.form =
      (fun p X => innerTransport U Uinv (C.form p X)) := by
    funext p X
    exact hForm p X
  unfold superconnectionCurvature
  rw [hDerivative p X Y, hFormEq, hParity]
  rw [innerTransport_gradedWedgeSquare C.form C.parity U Uinv p X Y hRight]
  exact (innerTransport_add U Uinv
    (C.derivative p X Y) (gradedWedgeSquare C.form C.parity p X Y)).symm

/-- Curvature transport follows from derivative covariance and the graded
wedge-square transport law. -/
theorem innerTransport_superconnectionCurvature
    (C : SuperConnection (Point := Point) (Tangent := Tangent) (Value := Value))
    (U Uinv : Value) (derivative' : Point → Tangent → Tangent → Value)
    (p : Point) (X Y : Tangent)
    (hRight : Uinv * U = 1)
    (hDerivative : innerTransport U Uinv (C.derivative p X Y) =
      derivative' p X Y) :
    innerTransport U Uinv (superconnectionCurvature C p X Y) =
      derivative' p X Y +
        gradedWedgeSquare
          (fun p X => innerTransport U Uinv (C.form p X))
          C.parity p X Y := by
  unfold superconnectionCurvature
  rw [innerTransport_add, hDerivative,
    innerTransport_gradedWedgeSquare C.form C.parity U Uinv p X Y hRight]

/-- In a field of characteristic different from two, the odd--odd product is
the complementary sum of the graded-symmetric and ordinary channels. -/
theorem odd_odd_product_decomposition
    {K : Type*} [Field K] [Algebra K Value] [NeZero (2 : K)]
    (ω : OperatorOneForm Point Tangent Value)
    (parity : Point → Tangent → Z2Parity)
    (p : Point) (X Y : Tangent)
    (hX : parity p X = Z2Parity.odd)
    (hY : parity p Y = Z2Parity.odd) :
    ω p X * ω p Y =
      InfoGeometry.Algebra.SupergradedBracket.gradedJordanProduct
          (R := K) true true (ω p X) (ω p Y) +
        (2 : K)⁻¹ •
          (gradedWedgeSquare ω parity p X Y) := by
  have h :=
    InfoGeometry.Algebra.SupergradedBracket.gradedProduct_decomposition
      (R := K) (A := Value) true true (ω p X) (ω p Y)
  simpa [gradedWedgeSquare, hX, hY,
    InfoGeometry.Algebra.SupergradedBracket.gradedJordanProduct,
    InfoGeometry.Algebra.InvariantTransport.anticommutator,
    InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.anticommutator,
    InfoGeometry.Algebra.SupergradedBracket.gradedSign] using h

end InfoGeometry.Optics.OperatorValuedConnection
