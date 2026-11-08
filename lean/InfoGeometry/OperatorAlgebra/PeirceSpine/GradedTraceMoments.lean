/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Cyclic moments and graded commutators

The dependency order is: cyclicity and product-power intertwining; Peirce
nilpotent corners and grading; graded commutator factorization; trace
cancellation. These statements are finite algebraic identities.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments

open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped BigOperators

variable {B R : Type*} [Ring B]

/-- A cyclic functional assigns equal positive-degree moments to `XY` and
`YX`. No idempotent or commutativity assumption is needed. -/
theorem cyclic_product_positive_power (τ : B → R)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X)) (X Y : B) (k : ℕ) :
    τ ((X * Y) ^ (k + 1)) = τ ((Y * X) ^ (k + 1)) := by
  calc
    τ ((X * Y) ^ (k + 1)) = τ (((X * Y) ^ k * X) * Y) := by
      rw [pow_succ, mul_assoc]
    _ = τ ((X * (Y * X) ^ k) * Y) := by rw [mul_pow_mul]
    _ = τ (Y * (X * (Y * X) ^ k)) := hCyc _ _
    _ = τ ((Y * X) ^ (k + 1)) := by rw [← mul_assoc, ← pow_succ']

/-- Positive-degree Peirce sheet moments have the same cyclic trace. -/
theorem peirce_sheet_positive_power_trace (τ : B → R)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X)) (P A C : B) (k : ℕ) :
    τ ((qgtPlus P A C) ^ (k + 1)) = τ ((qgtMinus P A C) ^ (k + 1)) := by
  exact cyclic_product_positive_power τ hCyc (conePlus P A) (coneMinus P C) k

/-- Every positive power of the Peirce metric, multiplied by the grading,
is exactly a commutator in the original noncommutative ring. -/
theorem grading_metric_power_eq_commutator {P : B} (hP : P * P = P)
    (A C : B) (k : ℕ) :
    invS P * (genV P A C) ^ (k + 1) =
      comm ((genV P A C) ^ k * conePlus P A) (coneMinus P C) := by
  have hS : Commute (invS P) (genV P A C) := by
    show invS P * genV P A C = genV P A C * invS P
    peirce_nf hP
  have hM : Commute (coneMinus P C) (genV P A C) := by
    show coneMinus P C * genV P A C = genV P A C * coneMinus P C
    peirce_nf hP
  have hSig : invS P * genV P A C = comm (conePlus P A) (coneMinus P C) := by
    peirce_nf hP
  calc
    invS P * (genV P A C) ^ (k + 1) =
        (genV P A C) ^ k * (invS P * genV P A C) := by
          rw [pow_succ, ← mul_assoc, (hS.pow_right k).eq, mul_assoc]
    _ = (genV P A C) ^ k * comm (conePlus P A) (coneMinus P C) := by rw [hSig]
    _ = comm ((genV P A C) ^ k * conePlus P A) (coneMinus P C) := by
      unfold comm
      calc
        _ = ((genV P A C) ^ k * conePlus P A) * coneMinus P C -
            ((genV P A C) ^ k * coneMinus P C) * conePlus P A := by noncomm_ring
        _ = ((genV P A C) ^ k * conePlus P A) * coneMinus P C -
            (coneMinus P C * (genV P A C) ^ k) * conePlus P A := by
              rw [(hM.pow_right k).eq]
        _ = _ := by simp only [mul_assoc]

/-- Every cyclic additive functional annihilates the graded positive-degree
metric moments. -/
theorem cyclic_grading_metric_power_zero [AddCommGroup R] (τ : B →+ R)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    τ (invS P * (genV P A C) ^ (k + 1)) = 0 := by
  rw [grading_metric_power_eq_commutator hP A C k]
  unfold comm
  rw [map_sub, hCyc, sub_self]

/-- Any finite integer linear combination of positive metric powers has
vanishing graded cyclic trace. -/
theorem cyclic_grading_metric_polynomial_zero [AddCommGroup R] (τ : B →+ R)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B)
    (s : Finset ℕ) (coeff : ℕ → ℤ) :
    τ (invS P * ∑ k ∈ s, (coeff k) • (genV P A C) ^ (k + 1)) = 0 := by
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro k hk
  rw [cyclic_grading_metric_power_zero τ hCyc hP A C k, smul_zero]

/-- Adding a finite positive-degree metric polynomial leaves the graded
cyclic trace of the unit unchanged. -/
theorem cyclic_grading_unit_add_polynomial [AddCommGroup R] (τ : B →+ R)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B)
    (s : Finset ℕ) (coeff : ℕ → ℤ) :
    τ (invS P * (1 + ∑ k ∈ s, (coeff k) • (genV P A C) ^ (k + 1))) =
      τ P - τ (1 - P) := by
  rw [mul_add, mul_one, map_add,
    cyclic_grading_metric_polynomial_zero τ hCyc hP A C s coeff, add_zero]
  unfold invS
  exact map_sub τ _ _

/-- Polynomial cancellation with coefficients in any commutative base ring,
for a linear cyclic functional on a possibly noncommutative algebra. -/
theorem cyclic_grading_algebra_polynomial_zero
    {K : Type*} [CommRing K] [Algebra K B] [AddCommGroup R] [Module K R]
    (τ : B →ₗ[K] R) (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B)
    (s : Finset ℕ) (coeff : ℕ → K) :
    τ (invS P * ∑ k ∈ s, (coeff k) • (genV P A C) ^ (k + 1)) = 0 := by
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k hk
  have hz : τ (invS P * (genV P A C) ^ (k + 1)) = 0 :=
    cyclic_grading_metric_power_zero τ.toAddMonoidHom hCyc hP A C k
  rw [hz, smul_zero]

/-- The graded trace of a unit plus any finite positive-degree polynomial
equals the trace difference of the complementary idempotent corners. -/
theorem cyclic_grading_unit_add_algebra_polynomial
    {K : Type*} [CommRing K] [Algebra K B] [AddCommGroup R] [Module K R]
    (τ : B →ₗ[K] R) (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B)
    (s : Finset ℕ) (coeff : ℕ → K) :
    τ (invS P * (1 + ∑ k ∈ s, (coeff k) • (genV P A C) ^ (k + 1))) =
      τ P - τ (1 - P) := by
  rw [mul_add, mul_one, map_add,
    cyclic_grading_algebra_polynomial_zero τ hCyc hP A C s coeff, add_zero]
  unfold invS
  exact map_sub τ _ _

end InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
