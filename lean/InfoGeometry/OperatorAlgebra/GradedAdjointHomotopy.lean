/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Left contracting homotopies for intrinsic graded adjoints

The homotopy is ordinary left multiplication by an odd CAR partner. It is not
the graded adjoint of that partner: two graded adjoints have inner curvature,
whereas their mixed pair with left multiplication retains the left CAR action.
The resulting exactness statements impose no dimension or topology on the
coefficient algebra.
-/

namespace InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The ordered mixed anticommutator needs only oddness of the left multiplier.
Involutivity and oddness of the charge are needed later for square-zero action. -/
theorem gradedAdjoint_mulLeft_anticommutator (θ : A ≃ₐ[R] A) (Q S : A)
    (hS : θ S = -S) :
    gradedAdjoint θ Q * LinearMap.mulLeft R S +
      LinearMap.mulLeft R S * gradedAdjoint θ Q =
        LinearMap.mulLeft R (Q * S + S * Q) := by
  apply LinearMap.ext
  intro x
  change Q * (S * x) - θ (S * x) * Q + S * (Q * x - θ x * Q) =
    (Q * S + S * Q) * x
  rw [map_mul, hS]
  noncomm_ring

/-- A CAR partner constructs a full contracting homotopy on the algebra. -/
theorem gradedAdjoint_mulLeft_contracts (θ : A ≃ₐ[R] A) (Q S : A)
    (hS : θ S = -S) (hCAR : Q * S + S * Q = 1) :
    gradedAdjoint θ Q * LinearMap.mulLeft R S +
      LinearMap.mulLeft R S * gradedAdjoint θ Q = 1 := by
  rw [gradedAdjoint_mulLeft_anticommutator θ Q S hS, hCAR]
  apply LinearMap.ext
  intro x
  change (1 : A) * x = x
  exact one_mul x

/-- Every cycle has the explicit primitive obtained by left multiplication. -/
theorem gradedAdjoint_cycle_primitive (θ : A ≃ₐ[R] A) (Q S : A)
    (hS : θ S = -S) (hCAR : Q * S + S * Q = 1)
    (x : A) (hx : gradedAdjoint θ Q x = 0) :
    gradedAdjoint θ Q (S * x) = x := by
  have h := congrArg (fun T : Module.End R A => T x)
    (gradedAdjoint_mulLeft_contracts θ Q S hS hCAR)
  change gradedAdjoint θ Q (S * x) + S * gradedAdjoint θ Q x = x at h
  simpa only [hx, mul_zero, add_zero] using h

/-- Nilpotence and the constructed homotopy give equality of native kernel and
range. No quotient or assumed cohomology witness is introduced. -/
theorem gradedAdjoint_ker_eq_range (θ : A ≃ₐ[R] A)
    (hθ : Function.Involutive θ) (Q S : A)
    (hQ : θ Q = -Q) (hS : θ S = -S)
    (hQsq : Q * Q = 0) (hCAR : Q * S + S * Q = 1) :
    LinearMap.ker (gradedAdjoint θ Q) = LinearMap.range (gradedAdjoint θ Q) := by
  ext x
  change gradedAdjoint θ Q x = 0 ↔ ∃ y, gradedAdjoint θ Q y = x
  constructor
  · intro hx
    exact ⟨S * x, gradedAdjoint_cycle_primitive θ Q S hS hCAR x hx⟩
  · rintro ⟨y, rfl⟩
    rw [gradedAdjoint_square_apply θ hθ Q hQ, hQsq,
      zero_mul, mul_zero, sub_self]

end InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
