/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition
import InfoGeometry.Core.IdempotentCartan
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # A global graded inner differential and its actual short complex

An involutive algebra automorphism supplies parity on the entire algebra.
The grading is applied to the argument, rather than supplied as an unchecked
Boolean tag. The Peirce specialization upgrades the existing reflection ring
equivalence, without changing its action or choosing a spectral basis.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- Global odd inner action: the twist carries the parity of the argument. -/
def twistedInner (θ : A →ₐ[R] A) (q : A) : Module.End R A :=
  LinearMap.mulLeft R q - (LinearMap.mulRight R q).comp θ.toLinearMap

/-- The opposite signed action. It is an adjoint only with a specified pairing. -/
def twistedCoInner (θ : A →ₐ[R] A) (q : A) : Module.End R A :=
  LinearMap.mulLeft R q + (LinearMap.mulRight R q).comp θ.toLinearMap

@[simp] theorem twistedInner_apply (θ : A →ₐ[R] A) (q x : A) :
    twistedInner R θ q x = q * x - θ x * q := rfl

@[simp] theorem twistedCoInner_apply (θ : A →ₐ[R] A) (q x : A) :
    twistedCoInner R θ q x = q * x + θ x * q := rfl

/-- The twisted Leibniz law holds on every element, homogeneous or not. -/
theorem twistedInner_leibniz (θ : A →ₐ[R] A) (q x y : A) :
    twistedInner R θ q (x * y) =
      twistedInner R θ q x * y + θ x * twistedInner R θ q y := by
  simp only [twistedInner_apply, map_mul]
  noncomm_ring

theorem twistedInner_even (θ : A →ₐ[R] A) (q x : A) (hx : θ x = x) :
    twistedInner R θ q x = lieOp R q x := by simp [hx]

theorem twistedInner_odd (θ : A →ₐ[R] A) (q x : A) (hx : θ x = -x) :
    twistedInner R θ q x = jordanOp R q x := by simp [hx]

theorem twistedInner_reverses_parity (θ : A →ₐ[R] A) {q : A}
    (hq : θ q = -q) (x : A) :
    θ (twistedInner R θ q x) = -twistedInner R θ q (θ x) := by
  simp only [twistedInner_apply, map_sub, map_mul, hq]
  noncomm_ring

/-- No factor of two and no characteristic restriction. -/
theorem twistedInner_square (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) :
    twistedInner R θ q * twistedInner R θ q = lieOp R (q * q) := by
  ext x
  change q * (q * x - θ x * q) - θ (q * x - θ x * q) * q =
    (q * q) * x - x * (q * q)
  simp only [map_sub, map_mul, hq, hθ x]
  noncomm_ring

theorem twistedCoInner_square (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) :
    twistedCoInner R θ q * twistedCoInner R θ q = lieOp R (q * q) := by
  ext x
  change q * (q * x + θ x * q) + θ (q * x + θ x * q) * q =
    (q * q) * x - x * (q * q)
  simp only [map_add, map_mul, hq, hθ x]
  noncomm_ring

theorem twistedInner_square_zero (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (hqq : q * q = 0) :
    twistedInner R θ q * twistedInner R θ q = 0 := by
  rw [twistedInner_square R θ hθ hq, hqq]
  ext x
  simp

/-- Two graded boundaries generate an ordinary inner action, not a positive Laplacian. -/
theorem twistedInner_mixed (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q r : A} (hq : θ q = -q) (hr : θ r = -r) :
    twistedInner R θ q * twistedInner R θ r +
      twistedInner R θ r * twistedInner R θ q = lieOp R (q * r + r * q) := by
  ext x
  change q * (r * x - θ x * r) - θ (r * x - θ x * r) * q +
    (r * (q * x - θ x * q) - θ (q * x - θ x * q) * r) =
    (q * r + r * q) * x - x * (q * r + r * q)
  simp only [map_sub, map_mul, hq, hr, hθ x]
  noncomm_ring

/-- Changing the second sign gives Jordan, rather than Lie, multiplication. -/
theorem twistedInner_coInner (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q r : A} (hq : θ q = -q) (hr : θ r = -r) :
    twistedInner R θ q * twistedCoInner R θ r +
      twistedCoInner R θ r * twistedInner R θ q = jordanOp R (q * r + r * q) := by
  ext x
  change q * (r * x + θ x * r) - θ (r * x + θ x * r) * q +
    (r * (q * x - θ x * q) + θ (q * x - θ x * q) * r) =
    (q * r + r * q) * x + x * (q * r + r * q)
  simp only [map_add, map_sub, map_mul, hq, hr, hθ x]
  noncomm_ring

/-- Boundaries lie in cycles as actual native submodules. -/
theorem twistedInner_range_le_ker (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (hqq : q * q = 0) :
    LinearMap.range (twistedInner R θ q) ≤ LinearMap.ker (twistedInner R θ q) := by
  rintro x ⟨y, rfl⟩
  change twistedInner R θ q (twistedInner R θ q y) = 0
  exact congrArg (fun f : Module.End R A => f y)
    (twistedInner_square_zero R θ hθ hq hqq)

/-- A genuine object in Mathlib's category of short complexes. -/
def twistedShortComplex (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (hqq : q * q = 0) :
    CategoryTheory.ShortComplex (ModuleCat R) :=
  CategoryTheory.ShortComplex.mk (ModuleCat.ofHom (twistedInner R θ q))
    (ModuleCat.ofHom (twistedInner R θ q)) (by
      ext x
      exact congrArg (fun f : Module.End R A => f x)
        (twistedInner_square_zero R θ hθ hq hqq))

/-- An algebra homomorphism intertwining the gradings intertwines the differential. -/
theorem twistedInner_natural {B : Type*} [Ring B] [Algebra R B]
    (θ : A →ₐ[R] A) (η : B →ₐ[R] B) (f : A →ₐ[R] B)
    (hf : ∀ x, f (θ x) = η (f x)) (q : A) :
    f.toLinearMap.comp (twistedInner R θ q) =
      (twistedInner R η (f q)).comp f.toLinearMap := by
  ext x
  change f (q * x - θ x * q) = f q * f x - η (f x) * f q
  simp only [map_sub, map_mul, hf]

open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition

/-- Scalar-compatible upgrade of the existing reflection ring equivalence. -/
def peirceTwist (p : A) (hp : p * p = p) : A ≃ₐ[R] A where
  toRingEquiv := reflectionConj p hp
  commutes' r := by
    change reflection p * algebraMap R A r * reflection p = algebraMap R A r
    rw [← (Algebra.commutes r (reflection p)).eq, mul_assoc, reflection_sq hp, mul_one]

@[simp] theorem peirceTwist_apply (p : A) (hp : p * p = p) (x : A) :
    peirceTwist R p hp x = reflection p * x * reflection p := rfl

theorem peirceTwist_involutive (p : A) (hp : p * p = p) :
    Function.Involutive (peirceTwist R p hp).toAlgHom := by
  intro x
  change reflection p * (reflection p * x * reflection p) * reflection p = x
  calc
    _ = (reflection p * reflection p) * x * (reflection p * reflection p) := by
      noncomm_ring
    _ = x := by rw [reflection_sq hp]; simp

theorem peirceTwist_forward (p : A) (hp : p * p = p) (a : A) :
    peirceTwist R p hp (component10 p a) = -component10 p a := by
  simp only [peirceTwist_apply, reflection, two_nsmul, component10, complementIdempotent]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- The concrete Peirce boundary is globally square-zero on the full algebra. -/
theorem peirce_boundary_square_zero (p : A) (hp : p * p = p) (a : A) :
    twistedInner R (peirceTwist R p hp).toAlgHom (component10 p a) *
      twistedInner R (peirceTwist R p hp).toAlgHom (component10 p a) = 0 := by
  exact twistedInner_square_zero R _ (peirceTwist_involutive R p hp)
    (peirceTwist_forward R p hp a)
    (InfoGeometry.Core.IdempotentCartan.corners_square_zero hp a).1

/-- A native short complex constructed from arbitrary forward Peirce data. -/
def peirceShortComplex (p : A) (hp : p * p = p) (a : A) :
    CategoryTheory.ShortComplex (ModuleCat R) :=
  twistedShortComplex R _ (peirceTwist_involutive R p hp)
    (peirceTwist_forward R p hp a)
    (InfoGeometry.Core.IdempotentCartan.corners_square_zero hp a).1

end InfoGeometry.OperatorAlgebra.LieJordan
