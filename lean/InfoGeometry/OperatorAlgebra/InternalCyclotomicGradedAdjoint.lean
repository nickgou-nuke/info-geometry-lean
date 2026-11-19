/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import InfoGeometry.Algebra.IsotropicCyclotomicGalois
import Mathlib.Algebra.Group.Hom.End

/-!
# A cubic twisted adjoint with a noncentral internal phase

The phase and charge belong to the same arbitrary associative ring. The
phase commutes only with the charge and is fixed by the automorphism; it
need not commute with an arbitrary argument. The cubic cyclotomic equation
cancels the mixed terms while preserving their ordered products.
-/

namespace InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint

open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
open InfoGeometry.Algebra.IsotropicCyclotomicGalois

variable {A : Type*} [Ring A]

/-- The exact cubic obstruction before imposing the cyclotomic equation.
The phase to the right of `θ (θ x)` is retained in its original order. -/
theorem ringGradedAdjoint_cube_defect (θ : A ≃+* A) (Q q : A)
    (hQ : θ Q = q * Q) (hq : θ q = q) (hqQ : Commute q Q) (x : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ Q (ringGradedAdjoint θ Q x)) =
      Q ^ 3 * x - cyclo3 q * Q ^ 2 * θ x * Q +
        cyclo3 q * Q * θ (θ x) * q * Q ^ 2 -
        θ (θ (θ x)) * q ^ 3 * Q ^ 3 := by
  have hQq : Q * q = q * Q := hqQ.eq.symm
  have hmove (a : A) : Q * (q * a) = q * (Q * a) := by
    rw [← mul_assoc, hQq, mul_assoc]
  simp only [ringGradedAdjoint_apply, map_sub, map_mul, hQ, hq, cyclo3]
  noncomm_ring [hQq, hmove]

/-- The internal cubic phase removes all mixed terms. No centrality of the
phase with respect to the argument is assumed. -/
theorem ringGradedAdjoint_cube_apply (θ : A ≃+* A) (Q q : A)
    (hQ : θ Q = q * Q) (hq : θ q = q) (hqQ : Commute q Q)
    (hcyclo : cyclo3 q = 0) (x : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ Q (ringGradedAdjoint θ Q x)) =
      Q ^ 3 * x - θ (θ (θ x)) * Q ^ 3 := by
  have hq3 : q ^ 3 = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using cyclo3_root_cube q hcyclo
  rw [ringGradedAdjoint_cube_defect θ Q q hQ hq hqQ]
  simp [hcyclo, hq3]

/-- Order-three covariance turns the cubic action into an inner derivation. -/
theorem ringGradedAdjoint_cube_eq_inner_apply (θ : A ≃+* A) (Q q : A)
    (hQ : θ Q = q * Q) (hq : θ q = q) (hqQ : Commute q Q)
    (hcyclo : cyclo3 q = 0) (hθ : ∀ x : A, θ (θ (θ x)) = x) (x : A) :
    ringGradedAdjoint θ Q (ringGradedAdjoint θ Q (ringGradedAdjoint θ Q x)) =
      Q ^ 3 * x - x * Q ^ 3 := by
  rw [ringGradedAdjoint_cube_apply θ Q q hQ hq hqQ hcyclo, hθ]

/-- The third power of the actual additive endomorphism vanishes precisely
when the charge cube is central in the full ring. -/
theorem ringGradedAdjoint_cube_eq_zero_iff (θ : A ≃+* A) (Q q : A)
    (hQ : θ Q = q * Q) (hq : θ q = q) (hqQ : Commute q Q)
    (hcyclo : cyclo3 q = 0) (hθ : ∀ x : A, θ (θ (θ x)) = x) :
    let δ : AddMonoid.End A := ringGradedAdjoint θ Q
    δ ^ 3 = 0 ↔ ∀ x : A, Commute (Q ^ 3) x := by
  dsimp only
  constructor
  · intro h x
    have hx := congrArg (fun T : AddMonoid.End A => T x) h
    change ringGradedAdjoint θ Q
      (ringGradedAdjoint θ Q (ringGradedAdjoint θ Q x)) = 0 at hx
    rw [ringGradedAdjoint_cube_eq_inner_apply θ Q q hQ hq hqQ hcyclo hθ] at hx
    change Q ^ 3 * x = x * Q ^ 3
    exact sub_eq_zero.mp hx
  · intro h
    apply AddMonoid.End.ext
    intro x
    change ringGradedAdjoint θ Q
      (ringGradedAdjoint θ Q (ringGradedAdjoint θ Q x)) = 0
    rw [ringGradedAdjoint_cube_eq_inner_apply θ Q q hQ hq hqQ hcyclo hθ]
    exact sub_eq_zero.mpr (h x).eq

end InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint
