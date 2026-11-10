/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SquareZeroSandwich
import Mathlib.Algebra.Lie.OfAssociative

/-! # Symmetric inner-derivation calculus on an associative algebra

The native endomorphism extends the existing matrix dissipator to arbitrary
associative algebras, including the existing real matrix-tower direct limit.
No adjoint relation, positivity, or spectral lower bound is assumed or inferred.
-/

namespace InfoGeometry.OperatorAlgebra.SymmetricDissipator

section RingDissipator

variable {A : Type*} [Ring A]

/-- Pure ring-level negative symmetric composition of two inner derivations on `[Ring A]`,
requiring no scalar `CommRing` or `Algebra` structure. -/
def ringDissipator (u v x : A) : A :=
  2 • (u * x * v + v * x * u) -
    ((u * v + v * u) * x + x * (u * v + v * u))

/-- Double-commutator form of `ringDissipator` over any associative ring `A`. -/
theorem ringDissipator_eq_double_commutator (u v x : A) :
    ringDissipator u v x =
      -(u * (v * x - x * v) - (v * x - x * v) * u +
        (v * (u * x - x * u) - (u * x - x * u) * v)) := by
  unfold ringDissipator
  simp only [two_nsmul]
  noncomm_ring

/-- The ring dissipator annihilates the multiplicative identity `1`. -/
theorem ringDissipator_one (u v : A) : ringDissipator u v 1 = 0 := by
  unfold ringDissipator
  simp only [mul_one, one_mul, two_nsmul]
  noncomm_ring

/-- Any ring homomorphism intertwines `ringDissipator`. -/
theorem map_ringDissipator {B : Type*} [Ring B]
    (f : A →+* B) (u v x : A) :
    f (ringDissipator u v x) =
      ringDissipator (f u) (f v) (f x) := by
  simp only [ringDissipator, two_nsmul, map_sub, map_add, map_mul]

/-- Simultaneous sign reversal of the two operator coefficients leaves `ringDissipator` invariant. -/
theorem ringDissipator_neg_neg (u v x : A) :
    ringDissipator (-u) (-v) x = ringDissipator u v x := by
  unfold ringDissipator
  simp only [two_nsmul]
  noncomm_ring

/-- A sign-reversing ring automorphism intertwines `ringDissipator`. -/
theorem ring_parity_equivariant (θ : A ≃+* A) (u v x : A)
    (hu : θ u = -u) (hv : θ v = -v) :
    θ (ringDissipator u v x) = ringDissipator u v (θ x) := by
  have h := map_ringDissipator θ.toRingHom u v x
  change θ (ringDissipator u v x) = ringDissipator (θ u) (θ v) (θ x) at h
  rwa [hu, hv, ringDissipator_neg_neg] at h

end RingDissipator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Negative symmetric composition of the two inner derivations. -/
def dissipator (u v : A) : Module.End R A :=
  -(LieAlgebra.ad R A u * LieAlgebra.ad R A v +
    LieAlgebra.ad R A v * LieAlgebra.ad R A u)

theorem dissipator_apply (u v x : A) :
    dissipator (R := R) u v x =
      2 • (u * x * v + v * x * u) -
        ((u * v + v * u) * x + x * (u * v + v * u)) := by
  change -(u * (v * x - x * v) - (v * x - x * v) * u +
    (v * (u * x - x * u) - (u * x - x * u) * v)) = _
  simp only [two_nsmul]
  noncomm_ring

/-- The extension agrees with the corrected finite full-matrix owner. -/
theorem matrix_dissipator {n : Type*} [Fintype n] [DecidableEq n]
    (u v : Matrix n n R) :
    dissipator (R := R) u v = Core.SquareZeroSandwich.symmDissipator u v := by
  ext x
  simp only [dissipator_apply, Core.SquareZeroSandwich.symmDissipator_apply,
    Core.SquareZeroSandwich.symmSandwich_apply, two_smul]

/-- This algebraic map annihilates the identity, for arbitrary coefficients. -/
theorem dissipator_one (u v : A) : dissipator (R := R) u v 1 = 0 := by
  simp only [dissipator_apply, mul_one, one_mul, two_smul, sub_self]

theorem map_dissipator {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (u v x : A) :
    f (dissipator (R := R) u v x) =
      dissipator (R := R) (f u) (f v) (f x) := by
  simp only [dissipator_apply, two_nsmul, map_sub, map_add, map_mul]

/-- Simultaneous sign reversal of the two coefficients leaves the action fixed. -/
theorem dissipator_neg_neg (u v : A) :
    dissipator (R := R) (-u) (-v) = dissipator (R := R) u v := by
  ext x
  simp [dissipator_apply]

/-- A sign-reversing ring automorphism intertwines the dissipator.
Involutivity is not needed for this general criterion. -/
theorem parity_equivariant (θ : A ≃+* A) (u v x : A)
    (hu : θ u = -u) (hv : θ v = -v) :
    θ (dissipator (R := R) u v x) = dissipator (R := R) u v (θ x) := by
  have h := map_dissipator (R := R) θ.toRingHom u v x
  change θ (dissipator (R := R) u v x) =
    dissipator (R := R) (θ u) (θ v) (θ x) at h
  rwa [hu, hv, dissipator_neg_neg] at h

/-- Every eigenspace of a sign-reversing algebra automorphism is invariant. -/
theorem parity_eigenspace_invariant (θ : A ≃ₐ[R] A) (u v x : A) (r : R)
    (hu : θ u = -u) (hv : θ v = -v) (hx : θ x = r • x) :
    θ (dissipator (R := R) u v x) = r • dissipator (R := R) u v x := by
  have h : θ (dissipator (R := R) u v x) =
      dissipator (R := R) u v (θ x) :=
    parity_equivariant (R := R) θ.toRingEquiv u v x hu hv
  rw [h, hx, map_smul]

/-- Naturality holds for every finite iterate, not merely one application. -/
theorem map_dissipator_iterate {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (u v x : A) (k : ℕ) :
    f ((dissipator (R := R) u v)^[k] x) =
      (dissipator (R := R) (f u) (f v))^[k] (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', map_dissipator, ih]

end InfoGeometry.OperatorAlgebra.SymmetricDissipator
