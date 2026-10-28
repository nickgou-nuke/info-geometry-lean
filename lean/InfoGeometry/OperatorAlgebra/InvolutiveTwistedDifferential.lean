/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.NoncommRing

/-!
# Twisted inner operators from an involutive algebra automorphism

For an algebra automorphism `θ`, the operator `q*x - θ(x)*q` obeys a
`θ`-twisted Leibniz rule. If `θ` is involutive and sends `q` to `-q`, its
square is the ordinary inner action of `q^2`; a square-zero `q` therefore
defines a genuine differential on the full algebra module.
-/

namespace InfoGeometry.OperatorAlgebra.InvolutiveTwistedDifferential

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The twisted inner action on the full algebra, represented as an
`R`-linear endomorphism. -/
def twistedInner (θ : A →ₐ[R] A) (q : A) : Module.End R A :=
  LinearMap.mulLeft R q - (LinearMap.mulRight R q).comp θ.toLinearMap

@[simp] theorem twistedInner_apply (θ : A →ₐ[R] A) (q x : A) :
    twistedInner θ q x = q * x - θ x * q := rfl

/-- The Leibniz rule is twisted by the automorphism on the left factor. -/
theorem twistedInner_leibniz (θ : A →ₐ[R] A) (q x y : A) :
    twistedInner θ q (x * y) =
      twistedInner θ q x * y + θ x * twistedInner θ q y := by
  simp only [twistedInner_apply, map_mul]
  noncomm_ring

/-- An odd generator for an involutive automorphism squares to its ordinary
inner action, with all coefficient order retained. -/
theorem twistedInner_square (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (x : A) :
    twistedInner θ q (twistedInner θ q x) = q * q * x - x * (q * q) := by
  simp only [twistedInner_apply, map_sub, map_mul, hq, hθ x]
  noncomm_ring

/-- A square-zero odd generator gives a square-zero endomorphism. -/
theorem twistedInner_square_zero (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (hqq : q * q = 0) :
    twistedInner θ q * twistedInner θ q = 0 := by
  ext x
  rw [show (twistedInner θ q * twistedInner θ q) x =
      twistedInner θ q (twistedInner θ q x) by rfl]
  rw [twistedInner_square θ hθ hq, hqq]
  simp

/-- Images are cycles for the square-zero twisted differential. -/
theorem twistedInner_range_le_ker (θ : A →ₐ[R] A)
    (hθ : Function.Involutive θ) {q : A} (hq : θ q = -q) (hqq : q * q = 0) :
    LinearMap.range (twistedInner θ q) ≤ LinearMap.ker (twistedInner θ q) := by
  rintro x ⟨y, rfl⟩
  change twistedInner θ q (twistedInner θ q y) = 0
  exact congrArg (fun f : Module.End R A => f y)
    (twistedInner_square_zero θ hθ hq hqq)

/-- Intertwining algebra homomorphisms transport the twisted inner action. -/
theorem twistedInner_natural {B : Type*} [Ring B] [Algebra R B]
    (θ : A →ₐ[R] A) (η : B →ₐ[R] B) (f : A →ₐ[R] B)
    (hf : ∀ x, f (θ x) = η (f x)) (q : A) :
    f.toLinearMap.comp (twistedInner θ q) =
      (twistedInner η (f q)).comp f.toLinearMap := by
  ext x
  change f (q * x - θ x * q) = f q * f x - η (f x) * f q
  rw [map_sub, map_mul, map_mul, hf]

end InfoGeometry.OperatorAlgebra.InvolutiveTwistedDifferential
