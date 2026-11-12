/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.WhiteheadStabilization
import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Hyperbolic transport of rectangular presentations

For a unit `U` in a matrix ring, its inverse-adjoint is the unit `star U⁻¹`.
Inverse and adjoint each reverse multiplication, so their composite is a
group homomorphism. The existing block-diagonal unit constructor then gives
the hyperbolic lift `diag(U, (U⁻¹)ᴴ)`.

This lift preserves the symmetric and skew off-diagonal forms, expressed
using the existing `SpinorialCore.Krein.IsIsometry` predicate. The rectangular
transport theorem retains the full ordered pairing `Xᴴ * Z`, with optional
independent generator changes on the right. In particular, its vanishing is
invariant under invertible presentation changes.

All coefficient operations take place in an arbitrary noncommutative
`StarRing`. The inverse is supplied by native matrix units, with no
determinant or nonsingular-inverse convention. This is the algebraic
dagger-orthogonality transport used by CSS presentations; it does not
construct a physical circuit or classify stabilizer phases.
-/

namespace InfoGeometry.Algebra.HyperbolicPresentationTransport

open Matrix
open InfoGeometry.Algebra.WhiteheadStabilization
open InfoGeometry.Canonical.SpinorialCore.Krein

section InverseAdjoint

variable {B : Type*} [Monoid B] [StarMul B]

/-- Inverse followed by adjoint is a homomorphism on the native unit group. -/
def inverseAdjoint : Bˣ →* Bˣ where
  toFun U := star U⁻¹
  map_one' := by simp
  map_mul' U V := by simp only [_root_.mul_inv_rev, star_mul]

@[simp]
theorem inverseAdjoint_apply (U : Bˣ) : inverseAdjoint U = star U⁻¹ := rfl

@[simp]
theorem coe_inverseAdjoint (U : Bˣ) :
    (inverseAdjoint U : B) = star (↑U⁻¹ : B) := rfl

/-- Applying inverse-adjoint twice recovers the original unit. -/
@[simp]
theorem inverseAdjoint_involutive (U : Bˣ) :
    inverseAdjoint (inverseAdjoint U) = U := by
  simp only [inverseAdjoint_apply, star_inv, inv_inv, star_star]

end InverseAdjoint

section Hyperbolic

variable {n A : Type*} [Fintype n] [DecidableEq n] [Ring A] [StarRing A]

/-- The hyperbolic lift of a change of frame to the primal and dual blocks. -/
def hyperbolicLift :
    (Matrix n n A)ˣ →* (Matrix (n ⊕ n) (n ⊕ n) A)ˣ where
  toFun U := blockDiagonalUnit U (inverseAdjoint U)
  map_one' := by
    change blockDiagonalUnit (1 : (Matrix n n A)ˣ) (inverseAdjoint 1) = 1
    rw [map_one, blockDiagonalUnit_one]
  map_mul' U V := by
    rw [map_mul, blockDiagonalUnit_mul]

@[simp]
theorem coe_hyperbolicLift (U : (Matrix n n A)ˣ) :
    (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A) =
      Matrix.fromBlocks (U : Matrix n n A) 0 0 (↑U⁻¹ : Matrix n n A)ᴴ := rfl

/-- The first diagonal block retains the original frame change. -/
theorem hyperbolicLift_injective :
    Function.Injective (hyperbolicLift :
      (Matrix n n A)ˣ → (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) := by
  intro U V h
  apply Units.ext
  have hval := congrArg Units.val h
  change Matrix.fromBlocks (U : Matrix n n A) 0 0 (↑U⁻¹ : Matrix n n A)ᴴ =
    Matrix.fromBlocks (V : Matrix n n A) 0 0 (↑V⁻¹ : Matrix n n A)ᴴ at hval
  exact (Matrix.fromBlocks_inj.mp hval).1

/-- Cancellation of an adjoint against its inverse-adjoint. -/
theorem adjoint_mul_inverseAdjoint (U : (Matrix n n A)ˣ) :
    (U : Matrix n n A)ᴴ * (↑U⁻¹ : Matrix n n A)ᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, U.inv_mul, Matrix.conjTranspose_one]

/-- Cancellation in the opposite order uses the other unit equation. -/
theorem inverseAdjoint_mul_adjoint (U : (Matrix n n A)ˣ) :
    (↑U⁻¹ : Matrix n n A)ᴴ * (U : Matrix n n A)ᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, U.mul_inv, Matrix.conjTranspose_one]

/-- The symmetric off-diagonal form on the primal and dual blocks. -/
def symmetricForm : Matrix (n ⊕ n) (n ⊕ n) A :=
  Matrix.fromBlocks 0 1 1 0

/-- The skew off-diagonal form, with the sign convention of `Matrix.J`. -/
def skewForm : Matrix (n ⊕ n) (n ⊕ n) A :=
  Matrix.fromBlocks 0 (-1) 1 0

omit [Fintype n] in
theorem symmetricForm_conjTranspose :
    (symmetricForm : Matrix (n ⊕ n) (n ⊕ n) A)ᴴ = symmetricForm := by
  simp [symmetricForm, Matrix.fromBlocks_conjTranspose]

omit [Fintype n] in
theorem skewForm_conjTranspose :
    (skewForm : Matrix (n ⊕ n) (n ⊕ n) A)ᴴ = -skewForm := by
  simp [skewForm, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

/-- The inverse-adjoint lift preserves the symmetric off-diagonal form. -/
theorem hyperbolicLift_preserves_symmetricForm (U : (Matrix n n A)ˣ) :
    IsIsometry (symmetricForm : Matrix (n ⊕ n) (n ⊕ n) A)
      (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A) := by
  change (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A)ᴴ * symmetricForm *
    (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A) = symmetricForm
  simp [coe_hyperbolicLift, symmetricForm, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, adjoint_mul_inverseAdjoint]

/-- The same lift preserves the skew off-diagonal form. -/
theorem hyperbolicLift_preserves_skewForm (U : (Matrix n n A)ˣ) :
    IsIsometry (skewForm : Matrix (n ⊕ n) (n ⊕ n) A)
      (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A) := by
  change (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A)ᴴ * skewForm *
    (hyperbolicLift U : Matrix (n ⊕ n) (n ⊕ n) A) = skewForm
  simp [coe_hyperbolicLift, skewForm, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, adjoint_mul_inverseAdjoint]

end Hyperbolic

section Rectangular

variable {n x z A : Type*} [Fintype n] [DecidableEq n] [Ring A] [StarRing A]

/-- Arbitrary rectangular presentations retain their full dagger pairing. -/
theorem daggerPairing_transport (U : (Matrix n n A)ˣ)
    (X : Matrix n x A) (Z : Matrix n z A) :
    ((U : Matrix n n A) * X)ᴴ * ((↑U⁻¹ : Matrix n n A)ᴴ * Z) = Xᴴ * Z := by
  rw [Matrix.conjTranspose_mul]
  calc
    (Xᴴ * (U : Matrix n n A)ᴴ) * ((↑U⁻¹ : Matrix n n A)ᴴ * Z) =
        Xᴴ * ((U : Matrix n n A)ᴴ * (↑U⁻¹ : Matrix n n A)ᴴ) * Z := by
          simp only [Matrix.mul_assoc]
    _ = Xᴴ * Z := by rw [adjoint_mul_inverseAdjoint, Matrix.mul_one]

/-- Vanishing of the dagger pairing is invariant under a physical frame change. -/
theorem daggerOrthogonality_transport_iff (U : (Matrix n n A)ˣ)
    (X : Matrix n x A) (Z : Matrix n z A) :
    ((U : Matrix n n A) * X)ᴴ * ((↑U⁻¹ : Matrix n n A)ᴴ * Z) = 0 ↔
      Xᴴ * Z = 0 := by
  rw [daggerPairing_transport]

variable {x' z' : Type*} [Fintype x] [Fintype z]

/-- Independent generator maps act on the two sides of the transported pairing. -/
theorem daggerPairing_transport_with_generators (U : (Matrix n n A)ˣ)
    (X : Matrix n x A) (Z : Matrix n z A)
    (V : Matrix x x' A) (W : Matrix z z' A) :
    ((U : Matrix n n A) * X * V)ᴴ * ((↑U⁻¹ : Matrix n n A)ᴴ * Z * W) =
      Vᴴ * (Xᴴ * Z) * W := by
  rw [Matrix.conjTranspose_mul]
  calc
    (Vᴴ * ((U : Matrix n n A) * X)ᴴ) *
        ((↑U⁻¹ : Matrix n n A)ᴴ * Z * W) =
      Vᴴ * (((U : Matrix n n A) * X)ᴴ *
        ((↑U⁻¹ : Matrix n n A)ᴴ * Z)) * W := by
          simp only [Matrix.mul_assoc]
    _ = Vᴴ * (Xᴴ * Z) * W := by rw [daggerPairing_transport]

/-- Arbitrary generator maps preserve an already vanishing pairing. -/
theorem daggerOrthogonality_transport_with_generators (U : (Matrix n n A)ˣ)
    (X : Matrix n x A) (Z : Matrix n z A)
    (V : Matrix x x' A) (W : Matrix z z' A) (h : Xᴴ * Z = 0) :
    ((U : Matrix n n A) * X * V)ᴴ * ((↑U⁻¹ : Matrix n n A)ᴴ * Z * W) = 0 := by
  rw [daggerPairing_transport_with_generators, h, Matrix.mul_zero, Matrix.zero_mul]

variable [DecidableEq x] [DecidableEq z]

/-- Invertible generator changes preserve and reflect dagger-orthogonality. -/
theorem daggerOrthogonality_transport_with_units_iff (U : (Matrix n n A)ˣ)
    (X : Matrix n x A) (Z : Matrix n z A)
    (V : (Matrix x x A)ˣ) (W : (Matrix z z A)ˣ) :
    ((U : Matrix n n A) * X * (V : Matrix x x A))ᴴ *
        ((↑U⁻¹ : Matrix n n A)ᴴ * Z * (W : Matrix z z A)) = 0 ↔
      Xᴴ * Z = 0 := by
  rw [daggerPairing_transport_with_generators]
  constructor
  · intro h
    calc
      Xᴴ * Z =
          ((↑V⁻¹ : Matrix x x A)ᴴ * (V : Matrix x x A)ᴴ) * (Xᴴ * Z) *
            ((W : Matrix z z A) * (↑W⁻¹ : Matrix z z A)) := by
              rw [inverseAdjoint_mul_adjoint, W.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (↑V⁻¹ : Matrix x x A)ᴴ *
          ((V : Matrix x x A)ᴴ * (Xᴴ * Z) * (W : Matrix z z A)) *
            (↑W⁻¹ : Matrix z z A) := by
              simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

end Rectangular

end InfoGeometry.Algebra.HyperbolicPresentationTransport
