/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.NoncommRing

/-!
# Intrinsic graded adjoint operators

An actual involutive algebra automorphism supplies parity on an associative
algebra. The odd adjoint is a native linear endomorphism, with its square equal
to the inner action of the charge square. No commutativity of the coefficient
algebra, scalar-centrality assumption, or external parity tag is used.

Algebra equivalences transport the parity and charge together. Fixed-parity
transport is stated separately with its necessary intertwining hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

section NoncommRingGradedAdjoint

variable {A B : Type*} [Ring A] [Ring B]

/-- The intrinsic odd adjoint over any associative ring `A`, bundled as an additive
group endomorphism `A →+ A` with respect to an involutive ring automorphism `θ : A ≃+* A`. -/
def ringGradedAdjoint (θ : A ≃+* A) (Q : A) : A →+ A where
  toFun X := Q * X - θ X * Q
  map_zero' := by simp
  map_add' X Y := by
    simp only [map_add]
    noncomm_ring

@[simp] theorem ringGradedAdjoint_apply (θ : A ≃+* A) (Q X : A) :
    ringGradedAdjoint θ Q X = Q * X - θ X * Q := rfl

/-- The graded Leibniz identity over any ring `A`. -/
theorem ringGradedAdjoint_leibniz (θ : A ≃+* A) (Q X Y : A) :
    ringGradedAdjoint θ Q (X * Y) =
      ringGradedAdjoint θ Q X * Y + θ X * ringGradedAdjoint θ Q Y := by
  simp only [ringGradedAdjoint_apply, map_mul]
  noncomm_ring

theorem ringGradedAdjoint_of_even (θ : A ≃+* A) (Q X : A) (hX : θ X = X) :
    ringGradedAdjoint θ Q X = Q * X - X * Q := by
  rw [ringGradedAdjoint_apply, hX]

theorem ringGradedAdjoint_of_odd (θ : A ≃+* A) (Q X : A) (hX : θ X = -X) :
    ringGradedAdjoint θ Q X = Q * X + X * Q := by
  rw [ringGradedAdjoint_apply, hX]
  simp only [neg_mul, sub_neg_eq_add]

theorem ringGradedAdjoint_parity (θ : A ≃+* A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    θ (ringGradedAdjoint θ Q X) = -ringGradedAdjoint θ Q (θ X) := by
  simp only [ringGradedAdjoint_apply, map_sub, map_mul, hQ, hθ X]
  noncomm_ring

/-- Over any ring `A`, the square of the odd graded adjoint is the inner commutator
derivation `[Q * Q, -]`. -/
theorem ringGradedAdjoint_square_apply (θ : A ≃+* A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ Q X) =
      (Q * Q) * X - X * (Q * Q) := by
  simp only [ringGradedAdjoint_apply, map_sub, map_mul, hQ, hθ X]
  noncomm_ring

theorem ringGradedAdjoint_square_apply_eq_zero_iff (θ : A ≃+* A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ Q X) = 0 ↔ Commute (Q * Q) X := by
  rw [ringGradedAdjoint_square_apply θ hθ Q hQ]
  change (Q * Q) * X - X * (Q * Q) = 0 ↔ (Q * Q) * X = X * (Q * Q)
  exact sub_eq_zero

theorem ringGradedAdjoint_mixed_apply (θ : A ≃+* A)
    (hθ : Function.Involutive θ) (Q S : A)
    (hQ : θ Q = -Q) (hS : θ S = -S) (X : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ S X) +
      ringGradedAdjoint θ S (ringGradedAdjoint θ Q X) =
        (Q * S + S * Q) * X - X * (Q * S + S * Q) := by
  simp only [ringGradedAdjoint_apply, map_sub, map_mul, hQ, hS, hθ X]
  noncomm_ring

theorem ringOdd_square_even (θ : A ≃+* A) (Q : A) (hQ : θ Q = -Q) :
    θ (Q * Q) = Q * Q := by
  rw [map_mul, hQ, neg_mul_neg]

theorem ringGradedAdjoint_curvature_closed (θ : A ≃+* A) (Q : A) (hQ : θ Q = -Q) :
    ringGradedAdjoint θ Q (Q * Q) = 0 := by
  rw [ringGradedAdjoint_apply, ringOdd_square_even θ Q hQ]
  noncomm_ring

def transportRingParity (e : A ≃+* B) (θ : A ≃+* A) : B ≃+* B :=
  (e.symm.trans θ).trans e

@[simp] theorem transportRingParity_apply (e : A ≃+* B) (θ : A ≃+* A) (X : B) :
    transportRingParity e θ X = e (θ (e.symm X)) := rfl

theorem map_ringGradedAdjoint (e : A ≃+* B) (θ : A ≃+* A) (Q X : A) :
    e (ringGradedAdjoint θ Q X) =
      ringGradedAdjoint (transportRingParity e θ) (e Q) (e X) := by
  simp only [ringGradedAdjoint_apply, map_sub, map_mul, transportRingParity_apply,
    RingEquiv.symm_apply_apply]

end NoncommRingGradedAdjoint

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]

/-- The intrinsic odd adjoint, bundled in the native endomorphism algebra. -/
def gradedAdjoint (θ : A ≃ₐ[R] A) (Q : A) : Module.End R A :=
  LinearMap.mulLeft R Q - (LinearMap.mulRight R Q).comp θ.toLinearMap

@[simp] theorem gradedAdjoint_apply (θ : A ≃ₐ[R] A) (Q X : A) :
    gradedAdjoint θ Q X = Q * X - θ X * Q := rfl

/-- The Leibniz identity uses the actual parity automorphism on the first factor. -/
theorem gradedAdjoint_leibniz (θ : A ≃ₐ[R] A) (Q X Y : A) :
    gradedAdjoint θ Q (X * Y) =
      gradedAdjoint θ Q X * Y + θ X * gradedAdjoint θ Q Y := by
  simp only [gradedAdjoint_apply, map_mul]
  noncomm_ring

theorem gradedAdjoint_of_even (θ : A ≃ₐ[R] A) (Q X : A)
    (hX : θ X = X) :
    gradedAdjoint θ Q X = Q * X - X * Q := by
  rw [gradedAdjoint_apply, hX]

theorem gradedAdjoint_of_odd (θ : A ≃ₐ[R] A) (Q X : A)
    (hX : θ X = -X) :
    gradedAdjoint θ Q X = Q * X + X * Q := by
  rw [gradedAdjoint_apply, hX]
  simp only [neg_mul, sub_neg_eq_add]

/-- Oddness of the charge makes the adjoint reverse actual parity. -/
theorem gradedAdjoint_parity (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    θ (gradedAdjoint θ Q X) = -gradedAdjoint θ Q (θ X) := by
  simp only [gradedAdjoint_apply, map_sub, map_mul, hQ, hθ X]
  noncomm_ring

/-- Parity reversal as an anticommutator identity between native linear maps. -/
theorem gradedAdjoint_parity_anticommutes (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) :
    θ.toLinearMap * gradedAdjoint θ Q +
      gradedAdjoint θ Q * θ.toLinearMap = 0 := by
  apply LinearMap.ext
  intro X
  change θ (gradedAdjoint θ Q X) + gradedAdjoint θ Q (θ X) = 0
  rw [gradedAdjoint_parity θ hθ Q hQ]
  exact neg_add_cancel _

/-- The square is an inner derivation, without a factor-of-two hypothesis. -/
theorem gradedAdjoint_square_apply (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    gradedAdjoint θ Q (gradedAdjoint θ Q X) =
      (Q * Q) * X - X * (Q * Q) := by
  simp only [gradedAdjoint_apply, map_sub, map_mul, hQ, hθ X]
  noncomm_ring

/-- Equality in the endomorphism algebra, rather than only pointwise notation. -/
theorem gradedAdjoint_square (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) :
    gradedAdjoint θ Q * gradedAdjoint θ Q =
      LinearMap.mulLeft R (Q * Q) - LinearMap.mulRight R (Q * Q) := by
  apply LinearMap.ext
  intro X
  exact gradedAdjoint_square_apply θ hθ Q hQ X

/-- Pointwise flatness is exactly membership in the centralizer of the square. -/
theorem gradedAdjoint_square_apply_eq_zero_iff (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) (X : A) :
    gradedAdjoint θ Q (gradedAdjoint θ Q X) = 0 ↔ Commute (Q * Q) X := by
  rw [gradedAdjoint_square_apply θ hθ Q hQ]
  change (Q * Q) * X - X * (Q * Q) = 0 ↔ (Q * Q) * X = X * (Q * Q)
  exact sub_eq_zero

/-- Square-zero action is equivalent to actual centrality of the charge square. -/
theorem gradedAdjoint_square_eq_zero_iff (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q : A) (hQ : θ Q = -Q) :
    gradedAdjoint θ Q * gradedAdjoint θ Q = 0 ↔
      ∀ X : A, Commute (Q * Q) X := by
  constructor
  · intro h X
    have hX := congrArg (fun T : Module.End R A => T X) h
    change gradedAdjoint θ Q (gradedAdjoint θ Q X) = 0 at hX
    exact (gradedAdjoint_square_apply_eq_zero_iff θ hθ Q hQ X).mp hX
  · intro h
    apply LinearMap.ext
    intro X
    change gradedAdjoint θ Q (gradedAdjoint θ Q X) = 0
    exact (gradedAdjoint_square_apply_eq_zero_iff θ hθ Q hQ X).mpr (h X)

/-- Two genuinely odd charges have the expected mixed inner curvature. -/
theorem gradedAdjoint_mixed_apply (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q S : A)
    (hQ : θ Q = -Q) (hS : θ S = -S) (X : A) :
    gradedAdjoint θ Q (gradedAdjoint θ S X) +
      gradedAdjoint θ S (gradedAdjoint θ Q X) =
        (Q * S + S * Q) * X - X * (Q * S + S * Q) := by
  simp only [gradedAdjoint_apply, map_sub, map_mul, hQ, hS, hθ X]
  noncomm_ring

theorem gradedAdjoint_mixed (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q S : A)
    (hQ : θ Q = -Q) (hS : θ S = -S) :
    gradedAdjoint θ Q * gradedAdjoint θ S +
      gradedAdjoint θ S * gradedAdjoint θ Q =
        LinearMap.mulLeft R (Q * S + S * Q) -
          LinearMap.mulRight R (Q * S + S * Q) := by
  apply LinearMap.ext
  intro X
  exact gradedAdjoint_mixed_apply θ hθ Q S hQ hS X

/-- The square of an odd charge is even. -/
theorem odd_square_even (θ : A ≃ₐ[R] A) (Q : A) (hQ : θ Q = -Q) :
    θ (Q * Q) = Q * Q := by
  rw [map_mul, hQ, neg_mul_neg]

/-- The operator curvature is closed under its own graded adjoint. -/
theorem gradedAdjoint_curvature_closed (θ : A ≃ₐ[R] A) (Q : A)
    (hQ : θ Q = -Q) :
    gradedAdjoint θ Q (Q * Q) = 0 := by
  rw [gradedAdjoint_apply, odd_square_even θ Q hQ]
  noncomm_ring

/-- Transport the actual algebra involution along an algebra equivalence. -/
def transportParity (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A) : B ≃ₐ[R] B :=
  (e.symm.trans θ).trans e

@[simp] theorem transportParity_apply (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A) (X : B) :
    transportParity e θ X = e (θ (e.symm X)) := rfl

theorem transportParity_involutive (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) :
    Function.Involutive (transportParity e θ) := by
  intro X
  simp only [transportParity_apply, AlgEquiv.symm_apply_apply,
    hθ (e.symm X), AlgEquiv.apply_symm_apply]

theorem transportParity_odd (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A)
    (Q : A) (hQ : θ Q = -Q) :
    transportParity e θ (e Q) = -(e Q) := by
  simp only [transportParity_apply, AlgEquiv.symm_apply_apply, hQ, map_neg]

/-- The parity and charge are transported together; no fixed-grading premise is hidden. -/
theorem map_gradedAdjoint (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A) (Q X : A) :
    e (gradedAdjoint θ Q X) =
      gradedAdjoint (transportParity e θ) (e Q) (e X) := by
  simp only [gradedAdjoint_apply, map_sub, map_mul, transportParity_apply,
    AlgEquiv.symm_apply_apply]

/-- Gauge/equivalence covariance as an equality of native endomorphisms. -/
theorem gradedAdjoint_conjugate (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A) (Q : A) :
    e.toLinearEquiv.conjAlgEquiv R (gradedAdjoint θ Q) =
      gradedAdjoint (transportParity e θ) (e Q) := by
  apply LinearMap.ext
  intro X
  change e (gradedAdjoint θ Q (e.symm X)) =
    gradedAdjoint (transportParity e θ) (e Q) X
  rw [map_gradedAdjoint, AlgEquiv.apply_symm_apply]

/-- With a fixed parity, the algebra equivalence must intertwine that parity. -/
theorem map_gradedAdjoint_of_intertwines
    (e : A ≃ₐ[R] B) (θ : A ≃ₐ[R] A) (φ : B ≃ₐ[R] B)
    (h : ∀ X : A, e (θ X) = φ (e X)) (Q X : A) :
    e (gradedAdjoint θ Q X) = gradedAdjoint φ (e Q) (e X) := by
  simp only [gradedAdjoint_apply, map_sub, map_mul, h X]

end InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
