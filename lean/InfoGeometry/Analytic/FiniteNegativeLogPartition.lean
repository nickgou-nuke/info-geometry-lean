/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analytic.LogSumExp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The finite negative log-partition potential

This is the unit-weight, inverse-temperature `-1` specialization of the
existing `InfoGeometry.Analytic.logSumExp`, with its sign reversed.

For a nonempty finite index type, Cauchy--Schwarz proves midpoint concavity
as the energies vary. A permutation and a common scalar subtraction from
the energies produce the same scalar subtraction from this potential.
The latter is an algebraic transformation law: no group cocycle, entropy
invariance, or Hessian nondegeneracy is inferred from the scalar shift.

Only the displayed midpoint inequality is claimed here. The singleton
readout records a permitted affine case, so no strict concavity is asserted.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Analytic.FiniteNegativeLogPartition

variable {ι : Type*} [Fintype ι]

/-- The negative of the existing finite unit-weight log-sum-exp potential. -/
def negativeLogPartition (energy : ι → ℝ) : ℝ :=
  -InfoGeometry.Analytic.logSumExp (fun _ => 1) energy (-1)

/-- Explicit finite exponential-sum readout of the existing statistical family. -/
theorem negativeLogPartition_eq (energy : ι → ℝ) :
    negativeLogPartition energy = -Real.log (∑ i, Real.exp (-energy i)) := by
  simp only [negativeLogPartition, logSumExp, logSumExpPartition,
    neg_one_mul, one_mul]

/-- Every nonempty finite unit-weight partition sum is strictly positive. -/
theorem partition_sum_pos [Nonempty ι] (energy : ι → ℝ) :
    0 < ∑ i, Real.exp (-energy i) := by
  simpa only [logSumExpPartition, neg_one_mul, one_mul] using
    logSumExp_sum_pos (fun _ : ι => (1 : ℝ)) energy
      (fun _ => zero_lt_one) (-1)

/-- Cauchy--Schwarz gives midpoint concavity of the negative log-partition
potential as a function of its finite energy vector. -/
theorem negativeLogPartition_midpoint [Nonempty ι] (energy energy' : ι → ℝ) :
    (negativeLogPartition energy + negativeLogPartition energy') / 2 ≤
      negativeLogPartition (fun i => (energy i + energy' i) / 2) := by
  classical
  simp only [negativeLogPartition_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.exp (-energy i / 2))
    (fun i => Real.exp (-energy' i / 2))
  have hMid :
      (∑ i, Real.exp (-energy i / 2) * Real.exp (-energy' i / 2)) =
        ∑ i, Real.exp (-((energy i + energy' i) / 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.exp_add]
    congr 1
    ring
  have hSq (e : ι → ℝ) :
      (∑ i, Real.exp (-e i / 2) ^ 2) = ∑ i, Real.exp (-e i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hMid, hSq energy, hSq energy'] at hCS
  have hLog := Real.log_le_log
    (pow_pos (partition_sum_pos (fun i => (energy i + energy' i) / 2)) 2) hCS
  rw [Real.log_pow,
    Real.log_mul (partition_sum_pos energy).ne' (partition_sum_pos energy').ne'] at hLog
  norm_num only [Nat.cast_ofNat] at hLog
  linarith

/-- Pullback of the midpoint inequality along any finite family of real linear
charges. No finite-dimensionality or nondegeneracy of the parameter module is needed. -/
theorem negativeLogPartition_midpoint_linear [Nonempty ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (charge : ι → V →ₗ[ℝ] ℝ) (x y : V) :
    (negativeLogPartition (fun i => charge i x) +
      negativeLogPartition (fun i => charge i y)) / 2 ≤
        negativeLogPartition (fun i => charge i ((1 / 2 : ℝ) • (x + y))) := by
  have hMid :
      (fun i => charge i ((1 / 2 : ℝ) • (x + y))) =
        (fun i => (charge i x + charge i y) / 2) := by
    funext i
    simp only [map_smul, map_add, smul_eq_mul]
    ring
  rw [hMid]
  exact negativeLogPartition_midpoint (fun i => charge i x) (fun i => charge i y)

/-- Reindexing the energies and subtracting a common scalar subtracts that
scalar from the negative log-partition potential. The hypothesis is an equality
of real energy values, with no group-action or cocycle interpretation supplied. -/
theorem negativeLogPartition_permute_sub [Nonempty ι]
    (energy energy' : ι → ℝ) (σ : Equiv.Perm ι) (c : ℝ)
    (hShift : ∀ i, energy' i = energy (σ i) - c) :
    negativeLogPartition energy' = negativeLogPartition energy - c := by
  classical
  rw [negativeLogPartition_eq, negativeLogPartition_eq]
  have hSum :
      (∑ i, Real.exp (-energy' i)) =
        Real.exp c * ∑ i, Real.exp (-energy i) := by
    calc
      (∑ i, Real.exp (-energy' i)) =
          ∑ i, Real.exp c * Real.exp (-energy (σ i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hShift i, neg_sub, sub_eq_add_neg, Real.exp_add]
      _ = Real.exp c * ∑ i, Real.exp (-energy (σ i)) := by
        rw [Finset.mul_sum]
      _ = Real.exp c * ∑ i, Real.exp (-energy i) := by
        rw [σ.sum_comp (fun i => Real.exp (-energy i))]
  rw [hSum, Real.log_mul (Real.exp_ne_zero c) (partition_sum_pos energy).ne',
    Real.log_exp]
  ring

/-- Permuting a finite energy vector leaves the potential unchanged. -/
theorem negativeLogPartition_permute [Nonempty ι]
    (energy : ι → ℝ) (σ : Equiv.Perm ι) :
    negativeLogPartition (fun i => energy (σ i)) = negativeLogPartition energy := by
  simpa only [sub_zero] using
    negativeLogPartition_permute_sub energy (fun i => energy (σ i)) σ 0
      (fun i => by simp)

/-- A common subtraction from every energy is a common subtraction from the
negative log-partition potential. -/
theorem negativeLogPartition_sub_const [Nonempty ι] (energy : ι → ℝ) (c : ℝ) :
    negativeLogPartition (fun i => energy i - c) = negativeLogPartition energy - c := by
  exact negativeLogPartition_permute_sub energy (fun i => energy i - c)
    (Equiv.refl ι) c (fun _ => rfl)

/-- With one state the potential is exactly its energy, an affine degeneracy
that rules out any unconditional strict-concavity interpretation. -/
theorem negativeLogPartition_unique [Unique ι] (energy : ι → ℝ) :
    negativeLogPartition energy = energy default := by
  rw [negativeLogPartition_eq, Fintype.sum_unique, Real.log_exp, neg_neg]

end InfoGeometry.Analytic.FiniteNegativeLogPartition

end
