/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in

/-!
# Summable errors along contractive refinement maps

The output may be any complete metric space. This file constructs compatible
limit *functions*. Linearity, positivity, and normalization require additional
algebraic hypotheses and are proved separately in `ApproximateStateLimits`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace ApproximateCompatibility

variable {A : ℕ → Type*} {E : Type*}

/-- Evaluate after a finite number of refinement steps, without dependent casts. -/
def evaluationSequence (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E) :
    (n : ℕ) → A n → ℕ → E
  | n, a, 0 => ω n a
  | n, a, k + 1 => evaluationSequence ι ω (n + 1) (ι n a) k

@[simp] theorem evaluationSequence_zero
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E) (n : ℕ) (a : A n) :
    evaluationSequence ι ω n a 0 = ω n a := rfl

@[simp] theorem evaluationSequence_succ
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E)
    (n : ℕ) (a : A n) (k : ℕ) :
    evaluationSequence ι ω n a (k + 1) =
      evaluationSequence ι ω (n + 1) (ι n a) k := rfl

variable [∀ n, SeminormedAddCommGroup (A n)] [MetricSpace E]

/-- Refinement preserves the one-step error bound at every later index. -/
theorem dist_evaluationSequence_succ_le
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hω : ∀ n (a : A n), dist (ω n a) (ω (n + 1) (ι n a)) ≤ ε n * ‖a‖)
    (k n : ℕ) (a : A n) :
    dist (evaluationSequence ι ω n a k) (evaluationSequence ι ω n a (k + 1)) ≤
      ε (n + k) * ‖a‖ := by
  induction k generalizing n with
  | zero => simpa using hω n a
  | succ k ih =>
    calc
      dist (evaluationSequence ι ω n a (k + 1))
          (evaluationSequence ι ω n a (k + 1 + 1)) ≤
          ε (n + 1 + k) * ‖ι n a‖ := ih (n + 1) (ι n a)
      _ ≤ ε (n + 1 + k) * ‖a‖ :=
        mul_le_mul_of_nonneg_left (hι n a) (hε _)
      _ = ε (n + (k + 1)) * ‖a‖ := by rw [Nat.add_right_comm n 1 k, Nat.add_assoc]

/-- Summable one-step errors make each refined evaluation sequence Cauchy. -/
theorem cauchySeq_evaluationSequence
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hω : ∀ n (a : A n), dist (ω n a) (ω (n + 1) (ι n a)) ≤ ε n * ‖a‖)
    (n : ℕ) (a : A n) : CauchySeq (evaluationSequence ι ω n a) := by
  apply cauchySeq_of_dist_le_of_summable (fun k => ε (n + k) * ‖a‖)
  · exact fun k => dist_evaluationSequence_succ_le ι ω ε hε hι hω k n a
  · exact (hSum.comp_injective (add_right_injective n)).mul_right ‖a‖

/-- Pointwise limits of approximately compatible functions are exactly compatible,
with a bound at every finite refinement horizon. -/
theorem exists_compatible_limit [CompleteSpace E]
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → E) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hω : ∀ n (a : A n), dist (ω n a) (ω (n + 1) (ι n a)) ≤ ε n * ‖a‖) :
    ∃ ωLimit : ∀ n, A n → E,
      (∀ n (a : A n), Tendsto (evaluationSequence ι ω n a) atTop (𝓝 (ωLimit n a))) ∧
      (∀ n (a : A n), ωLimit (n + 1) (ι n a) = ωLimit n a) ∧
      (∀ n (a : A n) k,
        dist (evaluationSequence ι ω n a k) (ωLimit n a) ≤
          (∑' j : ℕ, ε (n + k + j)) * ‖a‖) := by
  have hCauchy := cauchySeq_evaluationSequence ι ω ε hε hSum hι hω
  choose ωLimit hLimit using fun n (a : A n) =>
    cauchySeq_tendsto_of_complete (hCauchy n a)
  refine ⟨ωLimit, hLimit, ?_, ?_⟩
  · intro n a
    exact tendsto_nhds_unique (hLimit (n + 1) (ι n a))
      ((hLimit n a).comp (tendsto_add_atTop_nat 1))
  · intro n a k
    have hBound := dist_le_tsum_of_dist_le_of_tendsto
      (fun j => ε (n + j) * ‖a‖)
      (fun j => dist_evaluationSequence_succ_le ι ω ε hε hι hω j n a)
      ((hSum.comp_injective (add_right_injective n)).mul_right ‖a‖)
      (hLimit n a) k
    simpa only [← Nat.add_assoc, tsum_mul_right] using hBound

end ApproximateCompatibility
