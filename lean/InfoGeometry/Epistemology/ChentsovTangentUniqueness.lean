/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovUniqueness

/-!
# Chentsov uniqueness from tangent-only naturality

The family in `ChentsovUniqueness` assumes naturality on arbitrary coordinate
vectors. This module states the weaker, intrinsic condition on zero-sum tangent
vectors and derives the existing ambient interface by centering arbitrary
vectors at the base distribution. The centering is natural under the repository's
partition pushforwards because both probability weights and vectors push forward
by the same kernel.
-/

namespace InfoGeometry.Epistemology.ChentsovTangentUniqueness

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Epistemology.ChentsovUniqueness

/-! ## Causal layer 1: the tangent-only owner contract -/

/-- Raw coordinate vector `u` is tangent to the probability simplex iff its
coordinate sum is zero. -/
def IsTangent {α : Type} [Fintype α] (u : α → ℝ) : Prop :=
  ∑ i, u i = 0

/-- A symmetric bilinear family defined on simplex tangent vectors. The metric
evaluation itself requires zero-sum proofs; vectors outside the tangent space
are not inputs to `g`. -/
structure TangentInvariantMetricFamily where
  g : ∀ (α : Type) [Fintype α] (_P : ProbInterior α)
    (u : α → ℝ) (_hu : IsTangent u) (v : α → ℝ) (_hv : IsTangent v), ℝ
  add_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α)
    (u v w : α → ℝ) (hu : IsTangent u) (hv : IsTangent v) (hw : IsTangent w),
    g α P (u + v) (by
      change (∑ i, (u i + v i)) = 0
      rw [Finset.sum_add_distrib, hu, hv]
      simp) w hw = g α P u hu w hw + g α P v hv w hw
  smul_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (r : ℝ)
    (u w : α → ℝ) (hu : IsTangent u) (hw : IsTangent w),
    g α P (r • u) (by
      change (∑ i, r * u i) = 0
      rw [← Finset.mul_sum, hu]
      simp) w hw = r * g α P u hu w hw
  symm : ∀ (α : Type) [Fintype α] (P : ProbInterior α)
    (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v),
    g α P u hu v hv = g α P v hv u hu
  invariant_tangent : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α)
    (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v),
    g β (pushP E P) (pushV E u) (pushV_sum_zero E hu)
      (pushV E v) (pushV_sum_zero E hv) = g α P u hu v hv

/-- Every scalar multiple of the Fisher metric satisfies tangent-only
partition-embedding naturality. -/
noncomputable def scaledFisherTangentFamily (c : ℝ) : TangentInvariantMetricFamily where
  g := fun _ _ P u _ v _ => c * fisherMetric P u v
  add_left := fun _ _ P u v w _ _ _ => by rw [fisherMetric_add_left, mul_add]
  smul_left := fun _ _ P r u w _ _ => by
    rw [show r • u = fun a => r * u a from rfl, fisherMetric_smul_left, mul_left_comm]
  symm := fun _ _ P u v _ _ => by rw [fisherMetric_symm]
  invariant_tangent := by
    intro α β _ _ _ E P u v hu hv
    rw [fisherMetric_pushP]

/-- The Fisher metric supplies a closed inhabitant of the tangent-natural
family structure. -/
noncomputable instance : Inhabited TangentInvariantMetricFamily :=
  ⟨scaledFisherTangentFamily 1⟩

/-- The tangent-family evaluation of the canonical scaled Fisher example. -/
theorem scaledFisherTangentFamily_g (c : ℝ) {α : Type} [Fintype α]
    (P : ProbInterior α) (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v) :
    (scaledFisherTangentFamily c).g α P u hu v hv = c * fisherMetric P u v := rfl

/-! ## Causal layer 2: canonical centering and transport -/

/-- Remove the total-mass component relative to `P`; the result is tangent. -/
def center {α : Type} [Fintype α] (P : ProbInterior α) (u : α → ℝ) : α → ℝ :=
  fun i => u i - (∑ j, u j) * P.p i

theorem center_sum_zero {α : Type} [Fintype α] (P : ProbInterior α)
    (u : α → ℝ) : IsTangent (center P u) := by
  unfold IsTangent center
  calc
    (∑ i, (u i - (∑ j, u j) * P.p i)) =
        (∑ i, u i) - (∑ j, u j) * (∑ i, P.p i) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 0 := by rw [P.sum_one]; ring

theorem center_eq_self_of_tangent {α : Type} [Fintype α] (P : ProbInterior α)
    (u : α → ℝ) (hu : IsTangent u) : center P u = u := by
  funext i
  change u i - (∑ j, u j) * P.p i = u i
  rw [hu]
  simp

theorem center_add {α : Type} [Fintype α] (P : ProbInterior α)
    (u v : α → ℝ) : center P (u + v) = center P u + center P v := by
  funext i
  simp only [center, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem center_smul {α : Type} [Fintype α] (P : ProbInterior α)
    (r : ℝ) (u : α → ℝ) : center P (r • u) = r • center P u := by
  funext i
  change r * u i - (∑ j, r * u j) * P.p i = r * (u i - (∑ j, u j) * P.p i)
  rw [← Finset.mul_sum]
  ring

theorem pushV_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (u : α → ℝ) :
    ∑ b, pushV (α := α) (β := β) E u b = ∑ a, u a := by
  let K := (partitionEmbeddingToKernel E).kernel
  change ∑ b, pushforwardTangentVec K u b = ∑ a, u a
  unfold pushforwardTangentVec
  calc
    (∑ b, ∑ a, u a * K.T a b) = ∑ a, ∑ b, u a * K.T a b := Finset.sum_comm
    _ = ∑ a, u a * (∑ b, K.T a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
    _ = ∑ a, u a := by simp [K.sum_one]

theorem pushV_prob_eq_pushP_prob {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) :
    pushV (α := α) (β := β) E P.p = (pushP (α := α) (β := β) E P).p := by
  funext b
  rw [pushV_apply, pushP_apply]

theorem center_pushV {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (u : α → ℝ) :
    pushV (α := α) (β := β) E (center P u) =
      center (pushP (α := α) (β := β) E P) (pushV (α := α) (β := β) E u) := by
  have hmass : (∑ b, u (E.π b) * E.c b) = ∑ a, u a := by
    simpa only [pushV_apply] using pushV_sum E u
  funext b
  simp only [pushV_apply, center, pushP_apply]
  rw [hmass]
  ring

/-! ## Causal layer 3: tangent data induces an ambiently natural extension -/

/-- Extend a tangent metric to all coordinate vectors by first projecting them
onto the tangent space at the base distribution. -/
noncomputable def ambientExtension (F : TangentInvariantMetricFamily) : InvariantMetricFamily where
  g := fun α _ P u v =>
    F.g α P (center P u) (center_sum_zero P u) (center P v) (center_sum_zero P v)
  add_left := by
    intro α _ P u v w
    simpa only [center_add] using F.add_left α P (center P u) (center P v) (center P w)
      (center_sum_zero P u) (center_sum_zero P v) (center_sum_zero P w)
  smul_left := by
    intro α _ P r u w
    simpa only [center_smul] using F.smul_left α P r (center P u) (center P w)
      (center_sum_zero P u) (center_sum_zero P w)
  symm := by
    intro α _ P u v
    exact F.symm α P (center P u) (center P v)
      (center_sum_zero P u) (center_sum_zero P v)
  invariant := by
    intro α β _ _ _ E P u v
    simpa only [← center_pushV E P u, ← center_pushV E P v] using
      F.invariant_tangent E P (center P u) (center P v)
        (center_sum_zero P u) (center_sum_zero P v)

theorem ambientExtension_agrees_on_tangent (F : TangentInvariantMetricFamily)
    {α : Type} [Fintype α] (P : ProbInterior α) (u v : α → ℝ)
    (hu : IsTangent u) (hv : IsTangent v) :
    (ambientExtension F).g α P u v = F.g α P u hu v hv := by
  simp only [ambientExtension, center_eq_self_of_tangent P u hu,
    center_eq_self_of_tangent P v hv]

/-! ## Causal layer 4: rational Chentsov classification -/

/-- Tangent-only naturality suffices for Chentsov uniqueness at rational
interior distributions. The scale is common across all finite outcome types. -/
theorem chentsov_uniqueness_rational_tangent (F : TangentInvariantMetricFamily) :
    ∃ c : ℝ, ∀ (α : Type) [Fintype α] [DecidableEq α] (P : ProbInterior α),
      (∃ (N : ℕ) (m : α → ℕ), ∀ i, P.p i = m i / N) →
      ∀ u v : α → ℝ, (hu : IsTangent u) → (hv : IsTangent v) →
        F.g α P u hu v hv = c * fisherMetric P u v := by
  obtain ⟨c, hc⟩ := chentsov_uniqueness_rational (ambientExtension F)
  refine ⟨c, fun α _ _ P hP u v hu hv => ?_⟩
  rw [← ambientExtension_agrees_on_tangent F P u v hu hv]
  exact hc α P hP u v hu hv

end InfoGeometry.Epistemology.ChentsovTangentUniqueness
