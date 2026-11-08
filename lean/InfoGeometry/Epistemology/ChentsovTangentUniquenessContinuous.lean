/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.ChentsovTangentUniqueness
import InfoGeometry.Epistemology.ChentsovUniquenessContinuous

/-!
# Tangent-only Chentsov uniqueness at all interior distributions

This module extends the rational tangent-only uniqueness theorem using an
explicit sequential continuity assumption. Metric evaluations retain their
zero-sum tangent proofs throughout; rational approximation is reused from the
existing Chentsov continuity owner.
-/

namespace InfoGeometry.Epistemology.ChentsovTangentUniquenessContinuous

open Filter Topology
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Epistemology.ChentsovTangentUniqueness
open InfoGeometry.Epistemology.ChentsovUniqueness
open InfoGeometry.Epistemology.ChentsovUniquenessContinuous

/-- Tangent-metric evaluations vary continuously with the interior base point
for each fixed pair of tangent vectors. -/
def SeqContinuousTangent (F : TangentInvariantMetricFamily) : Prop :=
  ∀ (α : Type) [Fintype α] (Ps : ℕ → ProbInterior α) (P : ProbInterior α)
    (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v),
    Tendsto (fun k => (Ps k).p) atTop (𝓝 P.p) →
      Tendsto (fun k => F.g α (Ps k) u hu v hv) atTop (𝓝 (F.g α P u hu v hv))

/-- Every scaled Fisher tangent family satisfies tangent sequential continuity. -/
theorem scaledFisherTangentFamily_seqContinuous (c : ℝ) :
    SeqContinuousTangent (scaledFisherTangentFamily c) := by
  intro α _ Ps P u v hu hv hlim
  simpa only [scaledFisherTangentFamily_g] using
    (fisherMetric_tendsto u v hlim).const_mul c

/-- Tangent-only naturality and sequential continuity determine one common
Fisher scale on every finite simplex and every interior base point. -/
theorem chentsov_uniqueness_of_seqContinuous_tangent
    (F : TangentInvariantMetricFamily) (hF : SeqContinuousTangent F) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α]
      (P : ProbInterior α) (u v : α → ℝ)
      (hu : IsTangent u) (hv : IsTangent v),
      F.g α P u hu v hv = c * fisherMetric P u v := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_rational_tangent F
  refine ⟨c, fun α _ _ P u v hu hv => ?_⟩
  have hF_lim := hF α (ratApprox P) P u v hu hv (ratApprox_tendsto P)
  have hfish_lim := (fisherMetric_tendsto u v (ratApprox_tendsto P)).const_mul c
  have h_rat : (fun k => F.g α (ratApprox P k) u hu v hv) =
      fun k => c * fisherMetric (ratApprox P k) u v := by
    funext k
    exact hc α (ratApprox P k) (ratApprox_rational P k) u v hu hv
  rw [h_rat] at hF_lim
  exact tendsto_nhds_unique hF_lim hfish_lim

/-- The continuous tangent-only classification identifies the family with a
scaled Fisher metric on the tangent carrier. -/
theorem chentsov_classification_of_seqContinuous_tangent
    (F : TangentInvariantMetricFamily) (hF : SeqContinuousTangent F) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α]
      (P : ProbInterior α) (u v : α → ℝ)
      (hu : IsTangent u) (hv : IsTangent v),
      F.g α P u hu v hv = (scaledFisherTangentFamily c).g α P u hu v hv := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_of_seqContinuous_tangent F hF
  exact ⟨c, fun α _ _ P u v hu hv => by
    rw [hc α P u v hu hv]
    rfl⟩

/-- Positive definiteness on each tangent space forces the common continuous
Chentsov scale to be positive. -/
def PositiveDefiniteOnTangent (F : TangentInvariantMetricFamily) : Prop :=
  ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u : α → ℝ)
    (hu : IsTangent u), u ≠ 0 → 0 < F.g α P u hu u hu

/-- A positive definite, tangent-continuous invariant family has a strictly
positive Fisher scale. -/
theorem chentsov_scale_pos_of_positiveDefinite_tangent
    (F : TangentInvariantMetricFamily) (hF : SeqContinuousTangent F)
    (hpos : PositiveDefiniteOnTangent F) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (α : Type) [Fintype α] [DecidableEq α]
        (P : ProbInterior α) (u v : α → ℝ)
        (hu : IsTangent u) (hv : IsTangent v),
        F.g α P u hu v hv = c * fisherMetric P u v := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_of_seqContinuous_tangent F hF
  let u : Bool → ℝ := fun b => if b then 1 else -1
  have hu : IsTangent u := by
    change (∑ b : Bool, u b) = 0
    norm_num [u]
  have hu_ne : u ≠ 0 := by
    intro h
    have hfalse := congrFun h false
    norm_num [u] at hfalse
  let P : ProbInterior Bool := uniformInterior Bool
  have hFpos : 0 < F.g Bool P u hu u hu := hpos Bool P u hu hu_ne
  have hF_eq : F.g Bool P u hu u hu = c * fisherMetric P u u :=
    hc Bool P u u hu hu
  have hfish : 0 < fisherMetric P u u :=
    fisherMetric_pos_of_ne_zero P u hu_ne
  have hprod : 0 < c * fisherMetric P u u := by
    rw [← hF_eq]
    exact hFpos
  refine ⟨c, ?_, fun α _ _ P' u' v' hu' hv' => hc α P' u' v' hu' hv'⟩
  by_contra hcnonpos
  have hc_nonpos : c ≤ 0 := le_of_not_gt hcnonpos
  have hprod_nonpos : c * fisherMetric P u u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc_nonpos (le_of_lt hfish)
  exact (not_le_of_gt hprod) hprod_nonpos

end InfoGeometry.Epistemology.ChentsovTangentUniquenessContinuous
