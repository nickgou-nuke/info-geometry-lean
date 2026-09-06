import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Tactic

/-!
# Algebraic Zorn potential/gradient bridge

This owner formalizes the finite Zorn component calculation behind the usual
potential/gradient notation.  The coefficients live in a commutative ring,
so this is deliberately an algebraic carrier.  A differential operator,
product rule, gauge condition, or Maxwell equation requires a separate
calculus carrier and is not inferred here.
-/

namespace InfoGeometry.Canonical.ZornPotentialGradientAlgebraicBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

local notation "Vec3" => ZornVec3 R
local notation "ZM" => ZornVectorMatrix R

/-- Symmetric scalar/vector layout used for a potential-like Zorn element. -/
def symmetricField (scalar : R) (vector : Vec3) : ZM :=
  ⟨scalar, vector, fun i => -vector i, scalar⟩

/-- The algebraic analogue of a symmetric spacetime gradient layout. -/
def symmetricGradient (time : R) (gradient : Vec3) : ZM :=
  symmetricField time gradient

/-- The scalar/vector Peirce split of a symmetric Zorn potential layout. -/
theorem symmetricField_eq_diagonal_add_offDiagonal
    (scalar : R) (vector : Vec3) :
    symmetricField scalar vector =
      ZornVectorMatrix.add
        (ZornVectorMatrix.diagonal scalar scalar)
        (ZornVectorMatrix.offDiagonal vector (fun i => -vector i)) := by
  ext i <;> simp [symmetricField, ZornVectorMatrix.add,
    ZornVectorMatrix.diagonal, ZornVectorMatrix.offDiagonal]

/-- The upper vector component of the product of two symmetric fields. -/
def upperFieldComponent (time scalar : R) (gradient vector : Vec3) : Vec3 :=
  fun i => time * vector i + scalar * gradient i - cross gradient vector i

@[simp] theorem symmetricField_a (scalar : R) (vector : Vec3) :
    (symmetricField scalar vector).a = scalar := rfl

@[simp] theorem symmetricField_b (scalar : R) (vector : Vec3) :
    (symmetricField scalar vector).b = scalar := rfl

theorem symmetricGradient_mul_symmetricField
    (time scalar : R) (gradient vector : Vec3) :
    ZornVectorMatrix.mul (symmetricGradient time gradient)
      (symmetricField scalar vector) =
      ⟨time * scalar - dot gradient vector,
        upperFieldComponent time scalar gradient vector,
        fun i => -(upperFieldComponent time scalar gradient vector i),
        time * scalar - dot gradient vector⟩ := by
  ext i <;>
    simp [symmetricGradient, symmetricField, upperFieldComponent,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
  · ring
  · ring
  · ring

theorem symmetricGradient_mul_symmetricField_scalar
    (time scalar : R) (gradient vector : Vec3) :
    (ZornVectorMatrix.mul (symmetricGradient time gradient)
      (symmetricField scalar vector)).a =
      time * scalar - dot gradient vector := by
  rw [symmetricGradient_mul_symmetricField]

theorem symmetricGradient_mul_symmetricField_upper
    (time scalar : R) (gradient vector : Vec3) :
    (ZornVectorMatrix.mul (symmetricGradient time gradient)
      (symmetricField scalar vector)).v =
      upperFieldComponent time scalar gradient vector := by
  rw [symmetricGradient_mul_symmetricField]

theorem symmetricGradient_mul_symmetricField_lower
    (time scalar : R) (gradient vector : Vec3) :
    (ZornVectorMatrix.mul (symmetricGradient time gradient)
      (symmetricField scalar vector)).w =
      fun i => -(upperFieldComponent time scalar gradient vector i) := by
  rw [symmetricGradient_mul_symmetricField]

end InfoGeometry.Canonical.ZornPotentialGradientAlgebraicBridge
