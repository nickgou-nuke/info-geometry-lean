/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
import InfoGeometry.Algebra.NilpotentPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Exact polynomial calculus at Peirce corners

The ambient algebra is associative and may be noncommutative. At an
idempotent, the coefficient of a one-sided Peirce perturbation is the divided
difference `f(1) - f(0)`. It is not in general multiplication by `f'(P)`.
At an arbitrary noncommuting base, a square-zero perturbation can leave a
nonzero cubic remainder. The final theorem expresses the existing graded
moment cancellation using native `Polynomial.aeval`, including its constant
term. No analytic functional calculus or manifold structure is constructed.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialCalculus

open Polynomial GradedTraceMoments

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- A polynomial evaluated at an idempotent is determined by its scalar
values at zero and one. The ambient algebra need not be commutative. -/
theorem aeval_of_idempotent (f : R[X]) {P : B} (hP : P * P = P) :
    aeval P f = algebraMap R B (f.eval 0) +
      algebraMap R B (f.eval 1 - f.eval 0) * P := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, eval_add, hf, hg, map_sub]
      noncomm_ring
  | monomial n r =>
      cases n with
      | zero => simp
      | succ n =>
          have hp : P ^ (n + 1) = P :=
            IsIdempotentElem.pow_succ_eq n hP
          simp [Polynomial.aeval_monomial, hp]

/-- The exact polynomial increment along the upper Peirce corner. The
base idempotent and its nonzero corner do not commute. -/
theorem aeval_add_conePlus (f : R[X]) {P : B} (hP : P * P = P) (A : B) :
    aeval (P + conePlus P A) f = aeval P f +
      algebraMap R B (f.eval 1 - f.eval 0) * conePlus P A := by
  have hsum : (P + conePlus P A) * (P + conePlus P A) = P + conePlus P A := by
    peirce_nf hP
  rw [aeval_of_idempotent f hsum, aeval_of_idempotent f hP]
  noncomm_ring

/-- The same divided difference governs the lower Peirce direction, with
the opposite support routing retained. -/
theorem aeval_add_coneMinus (f : R[X]) {P : B} (hP : P * P = P) (C : B) :
    aeval (P + coneMinus P C) f = aeval P f +
      algebraMap R B (f.eval 1 - f.eval 0) * coneMinus P C := by
  have hsum : (P + coneMinus P C) * (P + coneMinus P C) = P + coneMinus P C := by
    peirce_nf hP
  rw [aeval_of_idempotent f hsum, aeval_of_idempotent f hP]
  noncomm_ring

/-- Square-zero alone leaves the separated word `N * X * N` in the cubic
expansion. This is the precise obstruction at a noncommuting base. -/
theorem cube_add_sqZero_remainder (X N : B) (hN : N * N = 0) :
    (X + N) ^ 3 - X ^ 3 - (X ^ 2 * N + X * N * X + N * X ^ 2) =
      N * X * N := by
  noncomm_ring [hN]

/-- A nonzero upper corner refutes the scalar-formal-derivative expression
for the square polynomial at the idempotent. -/
theorem square_add_conePlus_ne_formal_derivative {P : B}
    (hP : P * P = P) (A : B) (hN : conePlus P A ≠ 0) :
    (P + conePlus P A) ^ 2 ≠ P ^ 2 + (2 * P) * conePlus P A := by
  have hs : (P + conePlus P A) ^ 2 = P + conePlus P A := by
    rw [pow_two]
    peirce_nf hP
  have hr : P ^ 2 + (2 * P) * conePlus P A =
      P + (conePlus P A + conePlus P A) := by
    rw [pow_two, hP, mul_assoc, P_mul_conePlus hP, two_mul]
  rw [hs, hr]
  intro heq
  have hn : conePlus P A = conePlus P A + conePlus P A := add_left_cancel heq
  apply hN
  exact (add_left_cancel (by simpa only [add_zero] using hn) : 0 = conePlus P A).symm

section Cyclic

variable {M : Type*} [AddCommGroup M] [Module R M]
variable (τ : B →ₗ[R] M) (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))

include hCyc

/-- Cyclic linear readouts annihilate an upper Peirce corner. -/
theorem cyclic_conePlus_zero {P : B} (hP : P * P = P) (A : B) :
    τ (conePlus P A) = 0 := by
  calc
    τ (conePlus P A) = τ (P * conePlus P A) := by rw [P_mul_conePlus hP]
    _ = τ (conePlus P A * P) := hCyc _ _
    _ = 0 := by rw [conePlus_mul_P hP, map_zero]

/-- Polynomial readouts at an idempotent are unchanged by a one-sided
Peirce perturbation, even when the operators fail to commute. -/
theorem cyclic_aeval_add_conePlus (f : R[X]) {P : B}
    (hP : P * P = P) (A : B) :
    τ (aeval (P + conePlus P A) f) = τ (aeval P f) := by
  rw [aeval_add_conePlus f hP A, map_add, ← Algebra.smul_def,
    map_smul, cyclic_conePlus_zero τ hCyc hP A, smul_zero, add_zero]

/-- The graded cyclic readout of a polynomial in the Peirce metric depends
only on its constant term. The proof uses the division-free positive-power
commutator theorem, so no invertibility of two is required. -/
theorem cyclic_grading_aeval_metric (f : R[X]) {P : B}
    (hP : P * P = P) (A C : B) :
    τ (invS P * aeval (genV P A C) f) = f.eval 0 • τ (invS P) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, mul_add, hf, hg, eval_add, add_smul]
  | monomial n r =>
      cases n with
      | zero =>
          simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial,
            pow_zero, mul_one]
          rw [← Algebra.commutes r (invS P), ← Algebra.smul_def, map_smul]
      | succ n =>
          rw [Polynomial.aeval_monomial, ← Algebra.smul_def, mul_smul_comm,
            map_smul]
          have hz : τ (invS P * genV P A C ^ (n + 1)) = 0 :=
            cyclic_grading_metric_power_zero τ.toAddMonoidHom hCyc hP A C n
          rw [hz]
          simp

end Cyclic

end InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialCalculus
