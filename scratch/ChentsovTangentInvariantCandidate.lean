/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovUniqueness

/-!
# Candidate interface and finite Gram calculation for tangent-only Chentsov invariance

This scratch file records the tangent-only hypothesis shape and the uniform-point
Gram calculation. It is a proof candidate, not an owner theorem or accepted
Chentsov uniqueness result.
-/

namespace InfoGeometry.Epistemology.ChentsovTangentCandidate

open InfoGeometry.Epistemology.ChentsovUniqueness

/-- A vector is tangent to a finite probability simplex when its coordinate sum is zero. -/
def IsTangent {α : Type*} [Fintype α] (u : α → ℝ) : Prop :=
  ∑ i, u i = 0

/-- The root difference `eᵢ - eⱼ`, which is always tangent. -/
def rootDifference {α : Type*} [Fintype α] [DecidableEq α] (i j : α) : α → ℝ :=
  (Pi.single i (1 : ℝ)) - Pi.single j 1

/-- A centered coordinate vector at the uniform point: `eᵢ - (1/card α)·1`. -/
noncomputable def centeredCoord (α : Type) [Fintype α] [Nonempty α] [DecidableEq α]
    (i : α) : α → ℝ :=
  Pi.single i 1 - fun _ => 1 / (Fintype.card α : ℝ)

@[simp]
theorem centeredCoord_apply (α : Type) [Fintype α] [Nonempty α] [DecidableEq α]
    (i j : α) : centeredCoord α i j = Pi.single i 1 j - 1 / (Fintype.card α : ℝ) := rfl

theorem centeredCoord_tangent (α : Type) [Fintype α] [Nonempty α] [DecidableEq α]
    (i : α) : IsTangent (centeredCoord α i) := by
  unfold IsTangent centeredCoord
  rw [Finset.sum_sub_distrib]
  have h_single : ∑ j, Pi.single i (1 : ℝ) j = 1 := by
    classical
    simp [Pi.single_apply]
  have h_const : (∑ _j : α, (1 / (Fintype.card α : ℝ))) = 1 := by
    simpa [uniformInterior] using (uniformInterior α).sum_one
  rw [h_single, h_const, sub_self]

theorem centeredCoord_pushV_ofEquiv
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β] (σ : α ≃ β) (i : α) :
    pushV (ofEquiv σ) (centeredCoord α i) = centeredCoord β (σ i) := by
  funext b
  rw [pushV_apply]
  simp [centeredCoord, ofEquiv, Pi.single_apply, Equiv.symm_apply_eq]

theorem centeredCoord_reconstruct
    {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (u : α → ℝ) (hu : IsTangent u) :
    u = ∑ i, u i • centeredCoord α i := by
  classical
  funext j
  have h_single : (∑ i, u i * Pi.single i (1 : ℝ) j) = u j := by
    simp [Pi.single_apply]
  have h_const : (∑ i, u i * (1 / (Fintype.card α : ℝ))) = 0 := by
    rw [← Finset.sum_mul, hu]
    simp
  have h_eval : (∑ i, u i * centeredCoord α i j) = u j := by
    simp only [centeredCoord_apply, sub_mul, Finset.sum_sub_distrib]
    rw [h_single, h_const]
    simp
  simpa [Pi.smul_apply, smul_eq_mul] using h_eval.symm

/-- Metric-family data with naturality required only on tangent vectors. -/
structure TangentInvariantMetricFamily where
  g : ∀ (α : Type) [Fintype α], ProbInterior α → (α → ℝ) → (α → ℝ) → ℝ
  add_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u v w : α → ℝ),
    g α P (u + v) w = g α P u w + g α P v w
  smul_left : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (r : ℝ) (u w : α → ℝ),
    g α P (r • u) w = r * g α P u w
  symm : ∀ (α : Type) [Fintype α] (P : ProbInterior α) (u v : α → ℝ),
    g α P u v = g α P v u
  invariant_tangent : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (u v : α → ℝ),
    IsTangent u → IsTangent v →
    g β (pushP E P) (pushV E u) (pushV E v) =
    g α P u v

namespace TangentInvariantMetricFamily

variable (F : TangentInvariantMetricFamily) {α : Type} [Fintype α]

theorem zero_left (P : ProbInterior α) (w : α → ℝ) : F.g α P 0 w = 0 := by
  have h := F.smul_left α P 0 0 w
  rwa [zero_smul, zero_mul] at h

theorem sum_left {ι : Type} (P : ProbInterior α) (s : Finset ι) (f : ι → α → ℝ)
    (w : α → ℝ) : F.g α P (∑ i ∈ s, f i) w = ∑ i ∈ s, F.g α P (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using F.zero_left P w
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, F.add_left, ih]

theorem expand_centered [Nonempty α] [DecidableEq α]
    (P : ProbInterior α) (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v)
    :
    F.g α P u v = ∑ i, ∑ j, u i * v j *
      F.g α P (centeredCoord α i) (centeredCoord α j) := by
  classical
  rw [centeredCoord_reconstruct u hu]
  rw [F.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.symm, centeredCoord_reconstruct v hv, F.sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  change F.g α P (u i • centeredCoord α i) (v j • centeredCoord α j) = _
  calc
    F.g α P (u i • centeredCoord α i) (v j • centeredCoord α j) =
        F.g α P (v j • centeredCoord α j) (u i • centeredCoord α i) :=
      F.symm α P _ _
    _ = v j * F.g α P (centeredCoord α j) (u i • centeredCoord α i) :=
      F.smul_left α P (v j) _ _
    _ = v j * (u i * F.g α P (centeredCoord α i) (centeredCoord α j)) := by
      rw [F.symm α P (centeredCoord α j) (u i • centeredCoord α i),
        F.smul_left]
      ring
    _ = u i * v j * F.g α P (centeredCoord α i) (centeredCoord α j) := by ring

/-- Tangent Gram formula for a symmetric bilinear form whose centered-coordinate
Gram entries have a common diagonal and off-diagonal value. -/
theorem tangent_gram_formula [Nonempty α] [DecidableEq α]
    (P : ProbInterior α) {a b : ℝ}
    (h_diag : ∀ i, F.g α P (centeredCoord α i) (centeredCoord α i) = a)
    (h_off : ∀ i j, i ≠ j →
      F.g α P (centeredCoord α i) (centeredCoord α j) = b)
    (u v : α → ℝ) (hu : IsTangent u) (hv : IsTangent v) :
    F.g α P u v = (a - b) * ∑ i, u i * v i := by
  classical
  have h_entry : ∀ i j,
      u i * v j * F.g α P (centeredCoord α i) (centeredCoord α j) =
        u i * b * v j + if i = j then u i * v i * (a - b) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [h_diag]
      simp only [↓reduceIte]
      ring
    · rw [h_off i j hij]
      simp only [hij, ↓reduceIte]
      ring
  rw [F.expand_centered P u v hu hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun j _ => h_entry i j), Finset.sum_add_distrib,
    ← Finset.mul_sum, hv, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

end TangentInvariantMetricFamily

/-- Tangent-only naturality transports the centered Gram pairing under an
equivalence of finite outcome types. -/
theorem centeredGram_ofEquiv
    (F : TangentInvariantMetricFamily)
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β] (σ : α ≃ β) (i j : α) :
    F.g β (uniformInterior β) (centeredCoord β (σ i)) (centeredCoord β (σ j)) =
      F.g α (uniformInterior α) (centeredCoord α i) (centeredCoord α j) := by
  have h := F.invariant_tangent (ofEquiv σ) (uniformInterior α)
    (centeredCoord α i) (centeredCoord α j)
    (centeredCoord_tangent α i) (centeredCoord_tangent α j)
  rw [pushP_ofEquiv_uniform, centeredCoord_pushV_ofEquiv,
    centeredCoord_pushV_ofEquiv] at h
  exact h

/-- The intended conclusion at a uniform point, stated only on tangent vectors. -/
def HasUniformTangentScale (F : TangentInvariantMetricFamily)
    (α : Type) [Fintype α] [Nonempty α] (k : ℝ) : Prop :=
  ∀ (u v : α → ℝ), IsTangent u → IsTangent v →
    F.g α (uniformInterior α) u v = k * fisherMetric (uniformInterior α) u v

/-!
## Proof route recorded for the owner

Use the centered coordinate vectors `cᵢ := eᵢ - P.p`, where `P` is uniform.
Each `cᵢ` is tangent because `∑ eᵢ = 1 = ∑ P.p`; permutation naturality
therefore applies to their Gram entries. The equivalence pushforward sends
`cᵢ` to `c_(σ i)`. Permutations act transitively on diagonal pairs and on
ordered off-diagonal pairs, so the centered Gram matrix has a common diagonal
entry `a` and off-diagonal entry `b`.

For tangent `u`, the identity `u = ∑ i, u i • cᵢ` follows because the
uniform correction is `P.p j * (∑ i, u i) = 0`. Expand both arguments using
left bilinearity and symmetry; the same finite-sum calculation as
`gram_formula` then gives `F.g P u v = (a-b) ∑ i, u i*v i`. At the uniform
point `fisherMetric P u v = card(α) * ∑ i, u i*v i`, yielding a scale
without ever applying invariance to a non-tangent coordinate vector. This
also handles singleton and two-point types uniformly (with the singleton
tangent space trivial).

The formal proof obligations are: define the centered coordinate vector,
prove its tangent property, prove its permutation transport under `ofEquiv`,
prove the tangent centered-coordinate expansion, and adapt `gram_formula` to
that expansion. The existing `gram_formula` / `gram_perm` cannot be reused
verbatim because their Gram entries are evaluated on non-tangent `Pi.single`
vectors.
-/

end InfoGeometry.Epistemology.ChentsovTangentCandidate
