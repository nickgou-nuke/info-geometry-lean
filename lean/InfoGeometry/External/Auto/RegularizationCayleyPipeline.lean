import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Regularization, Cayley coordinates, and the unified adjoint

This file formalizes the algebraic part of the regularization pipeline.

The analytic boundedness claims are represented as explicit coordinate
contracts.  That is intentional: Lean should not hide the unbounded-operator
work behind a `sorry`.  The finite SymPy witness in
`regularization_cayley_pipeline.py` checks the concrete diagonal model.
-/

noncomputable section

namespace RegularizationCayleyPipeline

variable {A : Type*} [Ring A] [StarRing A]

/-- Relative regularization around the vacuum coordinate. -/
def regularize (T : A) : A := T - 1

/--
A squashed coordinate in the bounded stage is an element of a normed algebra.

There is no separate boundedness certificate: membership in a `NormedRing`
already gives the finite norm required by the bounded coordinate model.
-/
abbrev SquashedCoordinate (A : Type*) [NormedRing A] :=
  A

namespace SquashedCoordinate

variable {B : Type*} [NormedRing B]

/-- Historical projection name for the underlying bounded coordinate. -/
def value (x : SquashedCoordinate B) : B :=
  x

/-- Every normed-algebra coordinate is bounded by its own norm. -/
theorem bounded (x : SquashedCoordinate B) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖x.value‖ ≤ C :=
  ⟨‖x.value‖, norm_nonneg _, le_rfl⟩

end SquashedCoordinate

/-- A Cayley coordinate is represented by a unitary element.  This is the exact
bounded coordinate used in the colimit; recovering an unbounded generator is a
separate boundary operation requiring `1 - U` to be invertible. -/
structure CayleyCoordinate (A : Type*) [Ring A] [StarRing A] where
  unitary : A
  unitary_left : star unitary * unitary = 1
  unitary_right : unitary * star unitary = 1

namespace CayleyCoordinate

/-- The Cayley coordinate already lives in the bounded algebraic stage. -/
def value (U : CayleyCoordinate A) : A := U.unitary

@[simp] theorem star_mul_self (U : CayleyCoordinate A) :
    star U.value * U.value = 1 := U.unitary_left

@[simp] theorem self_mul_star (U : CayleyCoordinate A) :
    U.value * star U.value = 1 := U.unitary_right

end CayleyCoordinate

/-- Data required for the unified Dirac-Krein-Tomita adjoint.

In the finite algebraic layer we model `J` as an involutive self-adjoint
operator.  The analytic Tomita anti-linearity belongs to the Hilbert-space
completion layer; this record captures the multiplicative algebra contract used
by the bounded coordinates. -/
structure UnifiedAdjointData (A : Type*) [Ring A] [StarRing A] where
  eta : A
  J : A
  symmetry_self_adjoint : star (J * eta) = J * eta
  symmetry_involution : (J * eta) * (J * eta) = 1

namespace UnifiedAdjointData

variable (D : UnifiedAdjointData A)

/-- The composite boundary symmetry `K = J eta`. -/
def symmetry : A := D.J * D.eta

/-- The unified Dirac-Krein-Tomita adjoint.

The formula is expressed with the composite symmetry `K=J eta`:
`X^star = K X* K`.  Under `star K = K`, this is the algebraic form of
`J eta X* eta J`. -/
def adjoint (X : A) : A := D.symmetry * star X * D.symmetry

@[simp] theorem symmetry_star : star D.symmetry = D.symmetry := D.symmetry_self_adjoint

@[simp] theorem symmetry_sq : D.symmetry * D.symmetry = 1 := D.symmetry_involution

/-- The unified adjoint is an involution. -/
theorem adjoint_involution (X : A) : D.adjoint (D.adjoint X) = X := by
  let K : A := D.symmetry
  have hKstar : star K = K := by simp [K]
  have hKsq : K * K = 1 := by simp [K]
  calc
    D.adjoint (D.adjoint X) = K * star (K * star X * K) * K := by
      simp [adjoint, K, mul_assoc]
    _ = K * (star K * X * star K) * K := by simp [star_mul, mul_assoc]
    _ = K * (K * X * K) * K := by rw [hKstar]
    _ = (K * K) * X * (K * K) := by noncomm_ring
    _ = X := by simp [hKsq]

/-- The unified adjoint reverses multiplication. -/
theorem adjoint_mul (X Y : A) :
    D.adjoint (X * Y) = D.adjoint Y * D.adjoint X := by
  let K : A := D.symmetry
  have hKsq : K * K = 1 := by simp [K]
  calc
    D.adjoint (X * Y) = K * star (X * Y) * K := by
      simp [adjoint, K, mul_assoc]
    _ = K * (star Y * star X) * K := by simp [star_mul]
    _ = K * star Y * star X * K := by rw [mul_assoc K (star Y) (star X), mul_assoc]
    _ = (K * star Y * K) * (K * star X * K) := by
      rw [show (K * star Y * K) * (K * star X * K) =
          K * star Y * (K * K) * star X * K by noncomm_ring]
      simp [hKsq]
    _ = D.adjoint Y * D.adjoint X := by simp [adjoint, K, mul_assoc]

/-- The unified adjoint fixes the unit. -/
theorem adjoint_one : D.adjoint 1 = 1 := by
  calc
    D.adjoint 1 = D.symmetry * 1 * D.symmetry := by simp [adjoint]
    _ = D.symmetry * D.symmetry := by simp
    _ = 1 := D.symmetry_involution

/-- Taking the ordinary star after the unified adjoint is the same as applying
the unified adjoint to the ordinary star. -/
theorem star_adjoint (X : A) : star (D.adjoint X) = D.adjoint (star X) := by
  calc
    star (D.adjoint X) = star (D.symmetry * star X * D.symmetry) := by rfl
    _ = star D.symmetry * X * star D.symmetry := by simp [star_mul, mul_assoc]
    _ = D.symmetry * X * D.symmetry := by rw [D.symmetry_star]
    _ = D.adjoint (star X) := by simp [adjoint, mul_assoc]

/-- A Cayley coordinate remains unitary after applying the unified adjoint. -/
def mapCayley (U : CayleyCoordinate A) : CayleyCoordinate A where
  unitary := D.adjoint U.value
  unitary_left := by
    have hmul := D.adjoint_mul U.value (star U.value)
    have hstar : D.adjoint (star U.value) = star (D.adjoint U.value) :=
      (D.star_adjoint U.value).symm
    calc
      star (D.adjoint U.value) * D.adjoint U.value
          = D.adjoint (star U.value) * D.adjoint U.value := by rw [hstar]
      _ = D.adjoint (U.value * star U.value) := by rw [hmul]
      _ = D.adjoint 1 := by rw [show U.value * star U.value = 1 from U.unitary_right]
      _ = 1 := D.adjoint_one
  unitary_right := by
    have hmul := D.adjoint_mul (star U.value) U.value
    have hstar : D.adjoint (star U.value) = star (D.adjoint U.value) :=
      (D.star_adjoint U.value).symm
    calc
      D.adjoint U.value * star (D.adjoint U.value)
          = D.adjoint U.value * D.adjoint (star U.value) := by rw [hstar]
      _ = D.adjoint (star U.value * U.value) := by rw [hmul]
      _ = D.adjoint 1 := by rw [show star U.value * U.value = 1 from U.unitary_left]
      _ = 1 := D.adjoint_one

end UnifiedAdjointData

/-- Scalar Cayley transform used by the finite witness:
`C(t) = (t - i)/(t + i)`. -/
def scalarCayley (t : ℝ) : ℂ := ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)

/-- Relative scalar squashing argument `1 - t^{-1}`. -/
def scalarSquashArg (t : ℝ) : ℝ := 1 - t⁻¹

/-- Spectral squashing coordinate `tanh(1 - t^{-1})`. -/
def scalarSquash (t : ℝ) : ℝ := Real.tanh (scalarSquashArg t)

end RegularizationCayleyPipeline
