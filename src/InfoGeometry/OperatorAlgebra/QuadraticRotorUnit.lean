/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.InnerConjugation

/-! # Central-coefficient quadratic rotor units

The signature parameter is arbitrary. Its values `-1` and `1` give circular
and hyperbolic normalization respectively. The resulting automorphism is an
algebra automorphism; a star automorphism requires further hypotheses.
-/

namespace InfoGeometry.OperatorAlgebra.QuadraticRotor

section NoncommOperatorRotor

variable {A : Type*} [Ring A]

/-- Operator-valued polynomial rotor `c + s * J` in any associative ring `A`. -/
def opRotor (J c s : A) : A := c + s * J

/-- Over a general non-commutative ring `A`, the product of an operator rotor `c + s * J`
with its reverse `c - s * J` differs from `c * c - s * s * (J * J)` by the three explicit
commutator anomalies `[s, c] = s * c - c * s`, `[J, c] = J * c - c * J`, and
`[J, s] = J * s - s * J`. -/
theorem opRotor_mul_reverse_noncomm_anomaly (J c s : A) :
    opRotor J c s * opRotor J c (-s) - (c * c - s * s * (J * J)) =
      (s * c - c * s) * J + s * (J * c - c * J) - s * (J * s - s * J) * J := by
  unfold opRotor
  noncomm_ring

/-- When the operator coefficients `c, s` commute with each other and with `J`, the
commutator anomalies vanish and the quadratic norm `c * c - s * s * (J * J)` is recovered. -/
theorem opRotor_mul_reverse_of_comm (J c s : A)
    (hsc : s * c = c * s) (hJc : J * c = c * J) (hJs : J * s = s * J) :
    opRotor J c s * opRotor J c (-s) = c * c - s * s * (J * J) := by
  have h := opRotor_mul_reverse_noncomm_anomaly J c s
  rw [hsc, hJc, hJs] at h
  linear_combination (norm := noncomm_ring) h

end NoncommOperatorRotor

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The polynomial rotor in the full ambient associative algebra. -/
def rotor (J : A) (c s : R) : A := c • (1 : A) + s • J

theorem mul_reverse (J : A) (ε c s : R) (hJ : J * J = ε • (1 : A)) :
    rotor J c s * rotor J c (-s) = (c * c - ε * s * s) • (1 : A) := by
  simp only [rotor, add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hJ]
  module

/-- Both inverse laws are supplied, even over rings with zero divisors. -/
def unit (J : A) (ε c s : R) (hJ : J * J = ε • (1 : A))
    (hcs : c * c - ε * s * s = 1) : Aˣ where
  val := rotor J c s
  inv := rotor J c (-s)
  val_inv := by rw [mul_reverse J ε c s hJ, hcs, one_smul]
  inv_val := by
    have h := mul_reverse J ε c (-s) hJ
    simpa [hcs] using h

/-- Exact polynomial action on the anticommuting subspace. -/
theorem sandwich (J X : A) (ε c s : R) (hJ : J * J = ε • (1 : A))
    (hanti : J * X + X * J = 0) :
    rotor J c s * X * rotor J c (-s) =
      (c * c + ε * s * s) • X + (2 * c * s) • (J * X) := by
  have hXJ : X * J = -(J * X) := eq_neg_of_add_eq_zero_right hanti
  have hJXJ : J * X * J = -(ε • X) := by
    rw [mul_assoc, hXJ, mul_neg, ← mul_assoc, hJ, smul_mul_assoc, one_mul]
  calc
    _ = (c * c) • X - (c * s) • (X * J) +
        (s * c) • (J * X) - (s * s) • (J * X * J) := by
      simp only [rotor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    _ = _ := by rw [hXJ, hJXJ]; module

/-- Native scalar-preserving conjugation by the normalized rotor unit. -/
def equiv (J : A) (ε c s : R) (hJ : J * J = ε • (1 : A))
    (hcs : c * c - ε * s * s = 1) : A ≃ₐ[R] A :=
  AlgEquiv.ofRingEquiv (f := innerConjugationRingEquiv (unit J ε c s hJ hcs))
    (fun r => by
      change (unit J ε c s hJ hcs : A) * algebraMap R A r *
        (↑((unit J ε c s hJ hcs)⁻¹) : A) = algebraMap R A r
      rw [← Algebra.commutes r (unit J ε c s hJ hcs : A), mul_assoc]
      simp)

end InfoGeometry.OperatorAlgebra.QuadraticRotor
