/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import InfoGeometry.Algebra.Quantum.QBinomial

/-!
# Powers of the actual twisted adjoint at a primitive phase

The existing `gradedAdjoint θ Q` is used on the full associative algebra.
The phase in this file is a coefficient-field element. Its algebra image is
central, whereas neither the charge nor the argument is assumed central.
The separate internal cubic extension allows a noncentral operator phase.

The power identity is first proved without a periodicity assumption on `θ`.
Actual period `N` turns its residual action into the inner derivation of
`Q ^ N`, so zero N-th power is equivalent to centrality of that charge power.
-/

namespace InfoGeometry.OperatorAlgebra.CyclotomicGradedAdjoint

open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

section TwistedRight

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- The negative twisted right-multiplication summand of the existing adjoint. -/
def twistedRight (θ : A ≃ₐ[k] A) (Q : A) : Module.End k A :=
  -((LinearMap.mulRight k Q).comp θ.toLinearMap)

@[simp] theorem twistedRight_apply (θ : A ≃ₐ[k] A) (Q x : A) :
    twistedRight θ Q x = -(θ x * Q) := rfl

theorem gradedAdjoint_eq_left_add_twistedRight (θ : A ≃ₐ[k] A) (Q : A) :
    gradedAdjoint θ Q = LinearMap.mulLeft k Q + twistedRight θ Q := by
  simp only [gradedAdjoint, twistedRight, sub_eq_add_neg]

/-- Twisted right multiplication is left-semilinear for the actual automorphism. -/
theorem twistedRight_mul (θ : A ≃ₐ[k] A) (Q x y : A) :
    twistedRight θ Q (x * y) = θ x * twistedRight θ Q y := by
  simp only [twistedRight_apply, map_mul, mul_neg, mul_assoc]

/-- Every power is determined by its value at one and the iterated automorphism. -/
theorem twistedRight_pow_apply (θ : A ≃ₐ[k] A) (Q : A) (n : ℕ) (x : A) :
    (twistedRight θ Q ^ n) x = (θ ^ n) x * (twistedRight θ Q ^ n) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (twistedRight θ Q ^ (n + 1)) x =
            twistedRight θ Q ((twistedRight θ Q ^ n) x) := by
              rw [pow_succ', Module.End.mul_apply]
        _ = twistedRight θ Q ((θ ^ n) x * (twistedRight θ Q ^ n) 1) := by
              rw [ih]
        _ = θ ((θ ^ n) x) *
            twistedRight θ Q ((twistedRight θ Q ^ n) 1) :=
              twistedRight_mul θ Q _ _
        _ = (θ ^ (n + 1)) x * (twistedRight θ Q ^ (n + 1)) 1 := by
              simp only [pow_succ', AlgEquiv.mul_apply, Module.End.mul_apply]

theorem gradedAdjoint_pow_one (θ : A ≃ₐ[k] A) (Q : A)
    (n : ℕ) (hn : 0 < n) :
    (gradedAdjoint θ Q ^ n) 1 = 0 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      rw [pow_succ, Module.End.mul_apply]
      simp [gradedAdjoint_apply]

/-- Charge covariance is the ordered phase relation between the two summands. -/
theorem twistedRight_mulLeft (θ : A ≃ₐ[k] A) (Q : A) (q : k)
    (hQ : θ Q = q • Q) :
    twistedRight θ Q * LinearMap.mulLeft k Q =
      algebraMap k (Module.End k A) q *
        (LinearMap.mulLeft k Q * twistedRight θ Q) := by
  rw [← Algebra.smul_def]
  apply LinearMap.ext
  intro x
  change -(θ (Q * x) * Q) = q • (Q * -(θ x * Q))
  simp only [map_mul, hQ, smul_mul_assoc, smul_neg, mul_neg, mul_assoc]

end TwistedRight

section PrimitivePhase

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- At a primitive N-th phase, the N-th twisted-adjoint power has only its
two endpoint terms. The original automorphism action is retained explicitly. -/
theorem gradedAdjoint_pow_apply (θ : A ≃ₐ[k] A) (Q : A) (q : k)
    (n : ℕ) (hn : 1 < n) (hq : IsPrimitiveRoot q n)
    (hQ : θ Q = q • Q) (x : A) :
    (gradedAdjoint θ Q ^ n) x = Q ^ n * x - (θ ^ n) x * Q ^ n := by
  have hpow : gradedAdjoint θ Q ^ n =
      LinearMap.mulLeft k Q ^ n + twistedRight θ Q ^ n := by
    rw [gradedAdjoint_eq_left_add_twistedRight]
    exact InfoGeometry.Algebra.Quantum.q_comm_power q n hn hq _ _
      (twistedRight_mulLeft θ Q q hQ)
  have hone : (twistedRight θ Q ^ n) (1 : A) = -(Q ^ n) := by
    have h := congrArg (fun T : Module.End k A => T (1 : A)) hpow
    rw [gradedAdjoint_pow_one θ Q n (by omega), LinearMap.add_apply,
      LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, mul_one] at h
    calc
      (twistedRight θ Q ^ n) (1 : A) =
          (Q ^ n + (twistedRight θ Q ^ n) (1 : A)) - Q ^ n := by abel
      _ = -(Q ^ n) := by rw [← h]; simp
  calc
    (gradedAdjoint θ Q ^ n) x = Q ^ n * x + (twistedRight θ Q ^ n) x := by
      rw [hpow, LinearMap.add_apply, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
    _ = Q ^ n * x + (θ ^ n) x * (twistedRight θ Q ^ n) 1 := by
      rw [twistedRight_pow_apply]
    _ = Q ^ n * x - (θ ^ n) x * Q ^ n := by
      rw [hone, mul_neg, sub_eq_add_neg]

/-- Periodic covariance gives equality with an actual inner derivation in
the native noncommutative endomorphism algebra. -/
theorem gradedAdjoint_pow_eq_inner (θ : A ≃ₐ[k] A) (Q : A) (q : k)
    (n : ℕ) (hn : 1 < n) (hq : IsPrimitiveRoot q n)
    (hQ : θ Q = q • Q) (hθ : θ ^ n = 1) :
    gradedAdjoint θ Q ^ n =
      LinearMap.mulLeft k (Q ^ n) - LinearMap.mulRight k (Q ^ n) := by
  apply LinearMap.ext
  intro x
  rw [gradedAdjoint_pow_apply θ Q q n hn hq hQ, hθ, AlgEquiv.one_apply]
  rfl

/-- Nilpotency of the constructed differential is exactly centrality of the
charge power; the charge itself need not be nilpotent or central. -/
theorem gradedAdjoint_pow_eq_zero_iff (θ : A ≃ₐ[k] A) (Q : A) (q : k)
    (n : ℕ) (hn : 1 < n) (hq : IsPrimitiveRoot q n)
    (hQ : θ Q = q • Q) (hθ : θ ^ n = 1) :
    gradedAdjoint θ Q ^ n = 0 ↔ ∀ x : A, Commute (Q ^ n) x := by
  rw [gradedAdjoint_pow_eq_inner θ Q q n hn hq hQ hθ]
  constructor
  · intro h x
    have hx := congrArg (fun T : Module.End k A => T x) h
    change Q ^ n * x - x * Q ^ n = 0 at hx
    change Q ^ n * x = x * Q ^ n
    exact sub_eq_zero.mp hx
  · intro h
    apply LinearMap.ext
    intro x
    change Q ^ n * x - x * Q ^ n = 0
    exact sub_eq_zero.mpr (h x).eq

end PrimitivePhase

end InfoGeometry.OperatorAlgebra.CyclotomicGradedAdjoint
