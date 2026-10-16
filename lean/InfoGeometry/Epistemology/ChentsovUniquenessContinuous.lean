/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovUniqueness

/-!
# Ambient-invariant Fisher uniqueness on all interior points, under sequential continuity

`chentsov_uniqueness_rational` pins every ambiently invariant bilinear family to
`c • Fisher` on tangent vectors at rational interior distributions. Its invariance
assumption applies to arbitrary coordinate vectors, which is stronger than
tangent-only naturality. Here we add the **explicit hypothesis**
`SeqContinuous F`: along every sequence of interior distributions whose weight vectors
converge to the weight vector of an interior distribution `P`, the values `F.g α Pₖ u v`
converge to `F.g α P u v`. This is an assumption on the family, not an analytic
continuation.

Under this hypothesis the rational result extends to every interior distribution, via
the explicit rational approximation `ratApprox P k` with weights
`(⌊k P a⌋₊ + 1) / ∑ b, (⌊k P b⌋₊ + 1)`, the (proved) continuity of the Fisher metric,
and uniqueness of limits.
-/

namespace InfoGeometry.Epistemology.ChentsovUniquenessContinuous

open Finset Filter Topology
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Epistemology.ChentsovUniqueness

/-! ### 1. Sequential continuity hypothesis -/

/-- **Continuity hypothesis.** `F` is sequentially continuous in the base point: whenever
the weight vectors of interior distributions `Ps k` converge to the weight vector of the
interior distribution `P`, the values `F.g α (Ps k) u v` converge to `F.g α P u v`. -/
def SeqContinuous (F : InvariantMetricFamily) : Prop :=
  ∀ (α : Type) [Fintype α] (Ps : ℕ → ProbInterior α) (P : ProbInterior α) (u v : α → ℝ),
    Tendsto (fun k => (Ps k).p) atTop (𝓝 P.p) →
      Tendsto (fun k => F.g α (Ps k) u v) atTop (𝓝 (F.g α P u v))

/-- The Fisher metric is sequentially continuous in the base point. -/
theorem fisherMetric_tendsto {α : Type} [Fintype α] {Ps : ℕ → ProbInterior α}
    {P : ProbInterior α} (u v : α → ℝ) (h_lim : Tendsto (fun k => (Ps k).p) atTop (𝓝 P.p)) :
    Tendsto (fun k => fisherMetric (Ps k) u v) atTop (𝓝 (fisherMetric P u v)) := by
  unfold fisherMetric
  refine tendsto_finsetSum _ fun a _ => ?_
  exact tendsto_const_nhds.div (tendsto_pi_nhds.1 h_lim a) (ne_of_gt (P.pos a))

/-- Every scaled Fisher family satisfies the continuity hypothesis. -/
theorem scaledFisherFamily_seqContinuous (c : ℝ) : SeqContinuous (scaledFisherFamily c) :=
  fun _ _ _ _ u v h_lim => (fisherMetric_tendsto u v h_lim).const_mul c

/-- The Fisher family satisfies the continuity hypothesis. -/
theorem fisherFamily_seqContinuous : SeqContinuous fisherFamily :=
  scaledFisherFamily_seqContinuous 1

/-! ### 2. Rational approximation of an interior distribution -/

variable {α : Type} [Fintype α]

/-- Positive integer counts `⌊k P a⌋₊ + 1`. -/
noncomputable def ratCount (P : ProbInterior α) (k : ℕ) (a : α) : ℕ :=
  ⌊(k : ℝ) * P.p a⌋₊ + 1

/-- Total count `∑ a, ratCount P k a`. -/
noncomputable def ratTotal (P : ProbInterior α) (k : ℕ) : ℕ :=
  ∑ a, ratCount P k a

theorem ratCount_pos (P : ProbInterior α) (k : ℕ) (a : α) : 0 < ratCount P k a :=
  Nat.succ_pos _

theorem ratTotal_pos (P : ProbInterior α) (k : ℕ) : 0 < ratTotal P k := by
  obtain ⟨a⟩ := InvariantMetricFamily.nonempty_of_probInterior P
  exact lt_of_lt_of_le (ratCount_pos P k a)
    (Finset.single_le_sum (fun b _ => Nat.zero_le (ratCount P k b)) (Finset.mem_univ a))

theorem ratTotal_cast (P : ProbInterior α) (k : ℕ) :
    (ratTotal P k : ℝ) = ∑ a, (ratCount P k a : ℝ) := by
  rw [ratTotal, Nat.cast_sum]

/-- The rational approximation `ratApprox P k` with weights `ratCount P k a / ratTotal P k`. -/
noncomputable def ratApprox (P : ProbInterior α) (k : ℕ) : ProbInterior α where
  p a := (ratCount P k a : ℝ) / (ratTotal P k : ℝ)
  pos a := by
    have h_c := ratCount_pos P k a
    have h_t := ratTotal_pos P k
    positivity
  sum_one := by
    have h_t : (ratTotal P k : ℝ) ≠ 0 := by
      have := ratTotal_pos P k
      positivity
    rw [← Finset.sum_div, ← ratTotal_cast, div_self h_t]

/-- `ratApprox P k` is rational in the sense of `chentsov_uniqueness_rational`. -/
theorem ratApprox_rational (P : ProbInterior α) (k : ℕ) :
    ∃ (N : ℕ) (m : α → ℕ), ∀ i, (ratApprox P k).p i = m i / N :=
  ⟨ratTotal P k, ratCount P k, fun _ => rfl⟩

/-- Floor bound: `k P a < ratCount P k a`. -/
theorem ratCount_lower (P : ProbInterior α) (k : ℕ) (a : α) :
    (k : ℝ) * P.p a < ratCount P k a := by
  rw [ratCount, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- Floor bound: `ratCount P k a ≤ k P a + 1`. -/
theorem ratCount_upper (P : ProbInterior α) (k : ℕ) (a : α) :
    (ratCount P k a : ℝ) ≤ (k : ℝ) * P.p a + 1 := by
  rw [ratCount, Nat.cast_add, Nat.cast_one]
  have h_nonneg : 0 ≤ (k : ℝ) * P.p a := mul_nonneg (Nat.cast_nonneg k) (le_of_lt (P.pos a))
  linarith [Nat.floor_le h_nonneg]

/-- `ratCount P k a / k → P a`. -/
theorem ratCount_div_tendsto (P : ProbInterior α) (a : α) :
    Tendsto (fun k : ℕ => (ratCount P k a : ℝ) / k) atTop (𝓝 (P.p a)) := by
  have h_up : Tendsto (fun k : ℕ => P.p a + 1 / (k : ℝ)) atTop (𝓝 (P.p a)) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_add (P.p a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_up ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    rw [le_div_iff₀ hk', mul_comm]
    exact le_of_lt (ratCount_lower P k a)
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    rw [div_le_iff₀ hk', add_mul, one_div_mul_cancel (ne_of_gt hk'), mul_comm (P.p a)]
    exact ratCount_upper P k a

/-- `ratTotal P k / k → 1`. -/
theorem ratTotal_div_tendsto (P : ProbInterior α) :
    Tendsto (fun k : ℕ => (ratTotal P k : ℝ) / k) atTop (𝓝 1) := by
  have h_sum : Tendsto (fun k : ℕ => ∑ a, (ratCount P k a : ℝ) / k) atTop
      (𝓝 (∑ a, P.p a)) :=
    tendsto_finsetSum _ fun a _ => ratCount_div_tendsto P a
  rw [P.sum_one] at h_sum
  refine h_sum.congr fun k => ?_
  rw [ratTotal_cast, Finset.sum_div]

/-- Coordinatewise convergence `ratApprox P k a → P a`. -/
theorem ratApprox_apply_tendsto (P : ProbInterior α) (a : α) :
    Tendsto (fun k => (ratApprox P k).p a) atTop (𝓝 (P.p a)) := by
  have h_q := (ratCount_div_tendsto P a).div (ratTotal_div_tendsto P) one_ne_zero
  rw [div_one] at h_q
  refine h_q.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  show _ = (ratCount P k a : ℝ) / (ratTotal P k : ℝ)
  rw [Pi.div_apply, div_div_div_cancel_right₀ hk']

/-- The weight vectors of `ratApprox P k` converge to those of `P`. -/
theorem ratApprox_tendsto (P : ProbInterior α) :
    Tendsto (fun k => (ratApprox P k).p) atTop (𝓝 P.p) :=
  tendsto_pi_nhds.2 (ratApprox_apply_tendsto P)

/-! ### 3. Chentsov uniqueness on all interior points -/

/-- **Chentsov uniqueness under sequential continuity.** Assuming the continuity
hypothesis `SeqContinuous F`, there is a single constant `c` with
`F.g α P u v = c * fisherMetric P u v` for every finite type `α`, every interior
distribution `P` and all tangent vectors `u v`. -/
theorem chentsov_uniqueness_of_seqContinuous (F : InvariantMetricFamily)
    (hF : SeqContinuous F) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α] (P : ProbInterior α) (u v : α → ℝ),
      ∑ i, u i = 0 → ∑ i, v i = 0 → F.g α P u v = c * fisherMetric P u v := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_rational F
  refine ⟨c, fun α _ _ P u v hu hv => ?_⟩
  have h_F := hF α (ratApprox P) P u v (ratApprox_tendsto P)
  have h_fisher := (fisherMetric_tendsto u v (ratApprox_tendsto P)).const_mul c
  have h_eq : (fun k => F.g α (ratApprox P k) u v) =
      fun k => c * fisherMetric (ratApprox P k) u v :=
    funext fun k => hc α (ratApprox P k) (ratApprox_rational P k) u v hu hv
  rw [h_eq] at h_F
  exact tendsto_nhds_unique h_F h_fisher

/-- **Classification under sequential continuity.** Assuming `SeqContinuous F`, the
family `F` agrees with some `scaledFisherFamily c` on all tangent vectors at all interior
points. Conversely every `scaledFisherFamily c` is an invariant family satisfying the
continuity hypothesis (`scaledFisherFamily_seqContinuous`). -/
theorem chentsov_classification_of_seqContinuous (F : InvariantMetricFamily)
    (hF : SeqContinuous F) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α] (P : ProbInterior α) (u v : α → ℝ),
      ∑ i, u i = 0 → ∑ i, v i = 0 → F.g α P u v = (scaledFisherFamily c).g α P u v :=
  chentsov_uniqueness_of_seqContinuous F hF

/-- A family is positive definite on each simplex tangent space. -/
def IsPositiveDefiniteOnTangent (F : InvariantMetricFamily) : Prop :=
  ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u : α → ℝ),
    (∑ i, u i = 0) → u ≠ 0 → 0 < F.g α P u u

/-- If an invariant family is sequentially continuous and positive definite on
simplex tangent spaces, its Chentsov scale is strictly positive. -/
theorem chentsov_scale_pos_of_positiveDefinite (F : InvariantMetricFamily)
    (hF : SeqContinuous F) (hpos : IsPositiveDefiniteOnTangent F) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (α : Type) [Fintype α] [DecidableEq α] (P : ProbInterior α) (u v : α → ℝ),
        (∑ i, u i = 0) → (∑ i, v i = 0) →
          F.g α P u v = c * fisherMetric P u v := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_of_seqContinuous F hF
  let u : Bool → ℝ := fun b => if b then 1 else -1
  have hu : ∑ b : Bool, u b = 0 := by norm_num [u]
  have hu_ne : u ≠ 0 := by
    intro h
    have hfalse := congrFun h false
    norm_num [u] at hfalse
  let P : ProbInterior Bool := uniformInterior Bool
  have hFpos : 0 < F.g Bool P u u := hpos Bool P u hu hu_ne
  have hF_eq : F.g Bool P u u = c * fisherMetric P u u := hc Bool P u u hu hu
  have hfish : 0 < fisherMetric P u u := fisherMetric_pos_of_ne_zero P u hu_ne
  have hprod : 0 < c * fisherMetric P u u := by rw [← hF_eq]; exact hFpos
  refine ⟨c, ?_, fun α _ _ P' u' v' hu' hv' => hc α P' u' v' hu' hv'⟩
  by_contra hcnonpos
  have hc_nonpos : c ≤ 0 := le_of_not_gt hcnonpos
  have hprod_nonpos : c * fisherMetric P u u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc_nonpos (le_of_lt hfish)
  exact (not_le_of_gt hprod) hprod_nonpos

end InfoGeometry.Epistemology.ChentsovUniquenessContinuous
