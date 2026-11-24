/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Summable defects and compatible real readouts

Contractive successor maps and a summable bound on successive readout defects
produce pointwise limits that are exactly compatible. The quantitative error
is the remaining tail of the given error series, multiplied by the input norm.

The second section preserves native real `PositiveLinearMap`s and their value
on the distinguished element `1`. It supplies normalized positive linear readouts, not
a C-star algebra completion, a GNS representation, or a KMS state. No complex
scalar structure or C-star state carrier is introduced here.
-/

noncomputable section

open Filter
open scoped Topology

namespace InfoGeometry.Canonical.SummableCompatibleFunctionals

variable {A : ℕ → Type*}

/-- Pull a later readout back through a finite number of successor maps.
Recursing on the horizon avoids casts between the stage types. -/
def refinedReadout (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ) :
    (n : ℕ) → A n → ℕ → ℝ
  | n, a, 0 => ω n a
  | n, a, m + 1 => refinedReadout ι ω (n + 1) (ι n a) m

@[simp] theorem refinedReadout_zero
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ) (n : ℕ) (a : A n) :
    refinedReadout ι ω n a 0 = ω n a := rfl

@[simp] theorem refinedReadout_succ
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ)
    (n : ℕ) (a : A n) (m : ℕ) :
    refinedReadout ι ω n a (m + 1) =
      refinedReadout ι ω (n + 1) (ι n a) m := rfl

/-- Exact successor compatibility gives invariance under every finite
number of successive pullbacks. -/
theorem refinedReadout_eq_of_compatible
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ)
    (hω : ∀ n (a : A n), ω (n + 1) (ι n a) = ω n a)
    (n : ℕ) (a : A n) (m : ℕ) :
    refinedReadout ι ω n a m = ω n a := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      rw [refinedReadout_succ, ih, hω]

section SummableDefect

variable [∀ n, SeminormedAddCommGroup (A n)]

/-- Contractivity transports a one-step defect bound to any finite horizon. -/
theorem abs_refinedReadout_succ_sub_le
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hω : ∀ n (a : A n), |ω (n + 1) (ι n a) - ω n a| ≤ ε n * ‖a‖) :
    ∀ m n (a : A n),
      |refinedReadout ι ω n a (m + 1) - refinedReadout ι ω n a m| ≤
        ε (n + m) * ‖a‖ := by
  intro m
  induction m with
  | zero =>
      intro n a
      simpa only [refinedReadout_succ, refinedReadout_zero, Nat.add_zero] using hω n a
  | succ m ih =>
      intro n a
      calc
        |refinedReadout ι ω n a (m + 1 + 1) - refinedReadout ι ω n a (m + 1)| =
            |refinedReadout ι ω (n + 1) (ι n a) (m + 1) -
              refinedReadout ι ω (n + 1) (ι n a) m| := rfl
        _ ≤ ε (n + 1 + m) * ‖ι n a‖ := ih (n + 1) (ι n a)
        _ ≤ ε (n + 1 + m) * ‖a‖ :=
          mul_le_mul_of_nonneg_left (hι n a) (hε _)
        _ = ε (n + (m + 1)) * ‖a‖ := by
          simp only [Nat.add_assoc, Nat.add_comm 1 m]

/-- Summable real compatibility defects give exactly compatible pointwise
limits, with the explicit tail error bound. -/
theorem exists_compatible_limit_of_summable
    (ι : ∀ n, A n → A (n + 1)) (ω : ∀ n, A n → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hω : ∀ n (a : A n), |ω (n + 1) (ι n a) - ω n a| ≤ ε n * ‖a‖) :
    ∃ ω∞ : ∀ n, A n → ℝ,
      (∀ n (a : A n), Tendsto (refinedReadout ι ω n a) atTop (𝓝 (ω∞ n a))) ∧
      (∀ n (a : A n), ω∞ (n + 1) (ι n a) = ω∞ n a) ∧
      (∀ n (a : A n), |ω∞ n a - ω n a| ≤ (∑' k : ℕ, ε (n + k)) * ‖a‖) := by
  have hShift : ∀ n, Summable (fun m : ℕ => ε (n + m)) := by
    intro n
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).2 hSum
  have hDist : ∀ n (a : A n) m,
      dist (refinedReadout ι ω n a m) (refinedReadout ι ω n a (m + 1)) ≤
        ε (n + m) * ‖a‖ := by
    intro n a m
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_refinedReadout_succ_sub_le ι ω ε hε hι hω m n a
  have hCauchy : ∀ n (a : A n), CauchySeq (refinedReadout ι ω n a) := by
    intro n a
    exact cauchySeq_of_dist_le_of_summable
      (fun m => ε (n + m) * ‖a‖) (hDist n a) ((hShift n).mul_right ‖a‖)
  have hExists : ∀ n (a : A n),
      ∃ l : ℝ, Tendsto (refinedReadout ι ω n a) atTop (𝓝 l) :=
    fun n a => cauchySeq_tendsto_of_complete (hCauchy n a)
  let ω∞ : ∀ n, A n → ℝ := fun n a => Classical.choose (hExists n a)
  have hLimit : ∀ n (a : A n),
      Tendsto (refinedReadout ι ω n a) atTop (𝓝 (ω∞ n a)) :=
    fun n a => Classical.choose_spec (hExists n a)
  refine ⟨ω∞, hLimit, ?_, ?_⟩
  · intro n a
    have hTail : Tendsto (fun m => refinedReadout ι ω n a (m + 1))
        atTop (𝓝 (ω∞ n a)) :=
      (tendsto_add_atTop_iff_nat 1).2 (hLimit n a)
    exact tendsto_nhds_unique (hLimit (n + 1) (ι n a)) hTail
  · intro n a
    calc
      |ω∞ n a - ω n a| = dist (refinedReadout ι ω n a 0) (ω∞ n a) := by
        rw [refinedReadout_zero, Real.dist_eq, abs_sub_comm]
      _ ≤ ∑' m : ℕ, ε (n + m) * ‖a‖ :=
        dist_le_tsum_of_dist_le_of_tendsto₀
          (fun m => ε (n + m) * ‖a‖) (hDist n a)
          ((hShift n).mul_right ‖a‖) (hLimit n a)
      _ = (∑' m : ℕ, ε (n + m)) * ‖a‖ := (hShift n).tsum_mul_right ‖a‖

end SummableDefect

section PositiveReadouts

variable [∀ n, AddCommMonoid (A n)] [∀ n, PartialOrder (A n)] [∀ n, Module ℝ (A n)]

/-- The same finite pullback, retaining Mathlib's native positivity and
linearity rather than forgetting them to arbitrary scalar functions. -/
def refinedPositiveReadout (ι : ∀ n, A n →ₚ[ℝ] A (n + 1))
    (ω : ∀ n, A n →ₚ[ℝ] ℝ) : (n m : ℕ) → A n →ₚ[ℝ] ℝ
  | n, 0 => ω n
  | n, m + 1 => (refinedPositiveReadout ι ω (n + 1) m).comp (ι n)

@[simp] theorem refinedPositiveReadout_apply
    (ι : ∀ n, A n →ₚ[ℝ] A (n + 1)) (ω : ∀ n, A n →ₚ[ℝ] ℝ)
    (n m : ℕ) (a : A n) :
    refinedPositiveReadout ι ω n m a =
      refinedReadout (fun k => ι k) (fun k => ω k) n a m := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      change refinedPositiveReadout ι ω (n + 1) m (ι n a) =
        refinedReadout (fun k => ι k) (fun k => ω k) (n + 1) (ι n a) m
      exact ih (n + 1) (ι n a)

/-- Unital transition maps preserve normalization at each finite horizon. -/
theorem refinedPositiveReadout_one [∀ n, One (A n)]
    (ι : ∀ n, A n →ₚ[ℝ] A (n + 1)) (ω : ∀ n, A n →ₚ[ℝ] ℝ)
    (hι : ∀ n, ι n 1 = 1) (hω : ∀ n, ω n 1 = 1) (n m : ℕ) :
    refinedPositiveReadout ι ω n m 1 = 1 := by
  induction m generalizing n with
  | zero => exact hω n
  | succ m ih =>
      change refinedPositiveReadout ι ω (n + 1) m (ι n 1) = 1
      rw [hι n]
      exact ih (n + 1)

end PositiveReadouts

section PositiveLimits

variable [∀ n, SeminormedAddCommGroup (A n)] [∀ n, PartialOrder (A n)]
  [∀ n, Module ℝ (A n)] [∀ n, One (A n)]

/-- A summably defective family of normalized positive real linear readouts
has normalized positive real linear limits. Compatibility holds both for a
successor and for every finite sequence of transitions. -/
theorem exists_normalized_positive_compatible_limit
    (ι : ∀ n, A n →ₚ[ℝ] A (n + 1)) (ω : ∀ n, A n →ₚ[ℝ] ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hSum : Summable ε)
    (hι : ∀ n (a : A n), ‖ι n a‖ ≤ ‖a‖)
    (hι_one : ∀ n, ι n 1 = 1) (hω_one : ∀ n, ω n 1 = 1)
    (hω : ∀ n (a : A n), |ω (n + 1) (ι n a) - ω n a| ≤ ε n * ‖a‖) :
    ∃ ω∞ : ∀ n, A n →ₚ[ℝ] ℝ,
      (∀ n (a : A n),
        Tendsto (refinedReadout (fun k => ι k) (fun k => ω k) n a)
          atTop (𝓝 (ω∞ n a))) ∧
      (∀ n, (ω∞ (n + 1)).comp (ι n) = ω∞ n) ∧
      (∀ n m, refinedPositiveReadout ι ω∞ n m = ω∞ n) ∧
      (∀ n, ω∞ n 1 = 1) ∧
      (∀ n (a : A n), |ω∞ n a - ω n a| ≤ (∑' k : ℕ, ε (n + k)) * ‖a‖) := by
  obtain ⟨f, hLimit, hCompatible, hBound⟩ :=
    exists_compatible_limit_of_summable
      (fun n => ι n) (fun n => ω n) ε hε hSum hι hω
  have hPositiveLimit : ∀ n (a : A n),
      Tendsto (fun m => refinedPositiveReadout ι ω n m a) atTop (𝓝 (f n a)) := by
    intro n a
    simpa only [refinedPositiveReadout_apply] using hLimit n a
  let fLinear : ∀ n, A n →ₗ[ℝ] ℝ := fun n =>
    linearMapOfTendsto (f n)
      (fun m => (refinedPositiveReadout ι ω n m).toLinearMap)
      (tendsto_pi_nhds.mpr (hPositiveLimit n))
  let ω∞ : ∀ n, A n →ₚ[ℝ] ℝ := fun n =>
    PositiveLinearMap.mk (fLinear n) (by
      intro a b hab
      change f n a ≤ f n b
      exact le_of_tendsto_of_tendsto (hPositiveLimit n a) (hPositiveLimit n b)
        (Eventually.of_forall fun m => (refinedPositiveReadout ι ω n m).monotone hab))
  have hCorrected : ∀ n (a : A n), ω∞ (n + 1) (ι n a) = ω∞ n a := hCompatible
  refine ⟨ω∞, hLimit, ?_, ?_, ?_, hBound⟩
  · intro n
    ext a
    exact hCorrected n a
  · intro n m
    ext a
    rw [refinedPositiveReadout_apply]
    exact refinedReadout_eq_of_compatible (fun k => ι k) (fun k => ω∞ k)
      hCorrected n a m
  · intro n
    change f n (1 : A n) = 1
    refine tendsto_nhds_unique (hPositiveLimit n 1) ?_
    simpa only [refinedPositiveReadout_one ι ω hι_one hω_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)))

end PositiveLimits

end InfoGeometry.Canonical.SummableCompatibleFunctionals
