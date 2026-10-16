/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Export.LeanJuliaVerifiedInterop
import InfoGeometry.Epistemology.SubmersionSplitFinrank
import InfoGeometry.Epistemology.FisherNaturalGradientSteepest
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
# Certified Reference Contracts for Dual-Engine Geometric Computing

This module proves exact mathematical theorems over `ℕ`, `ℤ`, and `ℝ` corresponding
to the four reference contracts of the dual-engine scientific computing architecture.
These theorems are purely mathematical statements verified in the Lean 4 kernel over
exact integer, natural-number, and real-number types; they do not certify external
Julia runtime execution, C ABI linkers, or IEEE-754 floating-point hardware.

1. **Archetype I — Disjoint BitWord Blade Combinatorics & Graded Koszul Sign Commutation**:
   - Pointwise bitmask intersection `maskAnd` and disjointness predicate `MasksDisjoint`.
   - Additive Hamming weight law `maskWeight (maskXor u v) = maskWeight u + maskWeight v`
     for disjoint masks.
   - Disjoint inversion-count sum identity
     `maskInversionCount u v + maskInversionCount v u = maskWeight u * maskWeight v`
     and graded Koszul sign commutation law
     `maskInversionSign u v * maskInversionSign v u = koszulSign (maskParity u) (maskParity v)`.

2. **Archetype II — Submersion Horizontal Block Inverse, Zero Vertical Drift & Finrank Cubic Cost**:
   - Horizontal natural-gradient operator `truncatedNaturalGradient` and canonical horizontal
     sandwich operator `horizontalSandwich` on a `SubmersionSplit`.
   - Exact vanishing of vertical component (`projV = 0`), horizontal fixed-point invariance,
     range membership in `LinearMap.range split.projH`, normal-equation solution on horizontal
     gradients, and strict cubic finrank cost reduction.

3. **Archetype III — Chentsov Sufficient-Partition Compression & Steepest Ascent Preservation**:
   - Equivariance of `FisherNaturalGradientSteepest.expectation` and `fisherNaturalGradient`
     under pushforward along any `CongruentPartitionEmbedding`.
   - Preservation of Fisher natural-gradient differential pairing, squared norm / variance,
     and Cauchy–Schwarz steepest-ascent optimality under sufficient-statistic pushforward.

4. **Archetype IV — Safe KV-Cache Attention Sink Floor Renormalization & GNS Anchor Faithfulness**:
   - Anchor-floored weight update `flooredWeights` and normalized simplex distribution
     `renormalizedSinkWeights`.
   - Explicit lower bound `m / (1 + m) ≤ renormalizedSinkWeights w anchor m anchor` when
     `∑ i, w i = 1`, quantitative GNS column-energy lower bounds, and strict GNS quadratic
     positivity for operators supported on the anchor column.
-/

namespace InfoGeometry.Export.DualEngineCertifiedContracts

open Finset
open scoped BigOperators
open ChakravalaGA
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Export.LeanJuliaVerifiedInterop
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Epistemology.SubmersionSplitFinrank
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Epistemology.FisherNaturalGradientSteepest

/-!
## Archetype I: Disjoint BitWord Blade Combinatorics, Inversion-Count Sum Law & Graded Koszul Sign Commutation
-/

/-- Pointwise Boolean conjunction (bitwise AND) of two finite `BitWord` masks. -/
def maskAnd {n : ℕ} (u v : BitWord n) : BitWord n :=
  fun i => u i && v i

/-- Two `BitWord` masks are disjoint when no bit index is active in both masks simultaneously. -/
def MasksDisjoint {n : ℕ} (u v : BitWord n) : Prop :=
  ∀ i : Fin n, ¬(u i = true ∧ v i = true)

/-- Symmetry of bitmask disjointness. -/
theorem masksDisjoint_symm {n : ℕ} {u v : BitWord n} (h : MasksDisjoint u v) :
    MasksDisjoint v u := by
  intro i hvu
  exact h i ⟨hvu.2, hvu.1⟩

/-- Two masks are disjoint if and only if their bitwise AND is the all-false mask `maskZero n`. -/
theorem masksDisjoint_iff_maskAnd_eq_zero {n : ℕ} (u v : BitWord n) :
    MasksDisjoint u v ↔ maskAnd u v = maskZero n := by
  constructor
  · intro h
    funext i
    have hi := h i
    dsimp [maskAnd, maskZero]
    cases hu : u i <;> cases hv : v i
    · rfl
    · rfl
    · rfl
    · exfalso
      exact hi ⟨hu, hv⟩
  · intro h i huv
    have hi := congrFun h i
    dsimp [maskAnd, maskZero] at hi
    rw [huv.1, huv.2] at hi
    contradiction

/-- For disjoint masks, the active-bit support of `maskXor u v` is the union of the active-bit
supports of `u` and `v`. -/
theorem filter_maskXor_eq_union_of_disjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    Finset.univ.filter (fun i : Fin n => maskXor u v i = true) =
      Finset.univ.filter (fun i : Fin n => u i = true) ∪
        Finset.univ.filter (fun i : Fin n => v i = true) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [maskXor]
  have hi := hdisj i
  cases hu : u i <;> cases hv : v i
  · decide
  · decide
  · decide
  · exfalso
    exact hi ⟨hu, hv⟩

/-- For disjoint masks, the active-bit Finsets of `u` and `v` are disjoint. -/
theorem disjoint_filter_of_masksDisjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    Disjoint (Finset.univ.filter (fun i : Fin n => u i = true))
      (Finset.univ.filter (fun i : Fin n => v i = true)) := by
  rw [Finset.disjoint_filter]
  intro i _ hu hv
  exact hdisj i ⟨hu, hv⟩

/-- For disjoint masks, the Hamming weight of `maskXor u v` equals the sum of the Hamming
weights of `u` and `v`. -/
theorem maskXor_weight_of_disjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    maskWeight (maskXor u v) = maskWeight u + maskWeight v := by
  dsimp [maskWeight]
  rw [filter_maskXor_eq_union_of_disjoint hdisj]
  exact Finset.card_union_of_disjoint (disjoint_filter_of_masksDisjoint hdisj)

/-- The Cartesian product of the active-bit index sets of `u` and `v`. -/
def activeBitProduct {n : ℕ} (u v : BitWord n) : Finset (Fin n × Fin n) :=
  (Finset.univ.filter (fun i : Fin n => u i = true)) ×ˢ
    (Finset.univ.filter (fun j : Fin n => v j = true))

/-- The cardinality of `activeBitProduct u v` is the product of the Hamming weights. -/
theorem activeBitProduct_card {n : ℕ} (u v : BitWord n) :
    (activeBitProduct u v).card = maskWeight u * maskWeight v := by
  dsimp [activeBitProduct, maskWeight]
  exact Finset.card_product _ _

/-- The finite set of ordered active-bit pairs `(i, j)` with `i < j`, `u i = true`, and `v j = true`. -/
def upperPairs {n : ℕ} (u v : BitWord n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => decide (p.1 < p.2) && u p.1 && v p.2)

/-- When `u` and `v` are disjoint, no active pair lies on the diagonal `p.1 = p.2`, so
`activeBitProduct u v` partitions into `maskInversionPairs u v` and `upperPairs u v`. -/
theorem activeBitProduct_eq_union_of_disjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    activeBitProduct u v = maskInversionPairs u v ∪ upperPairs u v := by
  ext p
  simp only [activeBitProduct, maskInversionPairs, upperPairs, Finset.mem_product,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hu, hv⟩
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · exact Or.inr ⟨⟨hlt, hu⟩, hv⟩
    · exfalso
      have hv1 : v p.1 = true := by
        rw [heq]
        exact hv
      exact hdisj p.1 ⟨hu, hv1⟩
    · exact Or.inl ⟨⟨hgt, hu⟩, hv⟩
  · rintro (⟨⟨_, hu⟩, hv⟩ | ⟨⟨_, hu⟩, hv⟩) <;> exact ⟨hu, hv⟩

/-- The lower inversion pairs (`p.2 < p.1`) and upper ordered pairs (`p.1 < p.2`) are disjoint. -/
theorem disjoint_maskInversionPairs_upperPairs {n : ℕ} (u v : BitWord n) :
    Disjoint (maskInversionPairs u v) (upperPairs u v) := by
  dsimp only [maskInversionPairs, upperPairs]
  rw [Finset.disjoint_filter]
  intro p _ h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  exact lt_asymm h1.1.1 h2.1.1

/-- Coordinate swap `(i, j) ↦ (j, i)` gives a bijection between `upperPairs u v` and
`maskInversionPairs v u`. -/
theorem upperPairs_card_eq_maskInversionCount_symm {n : ℕ} (u v : BitWord n) :
    (upperPairs u v).card = maskInversionCount v u := by
  dsimp [upperPairs, maskInversionCount, maskInversionPairs]
  apply Finset.card_bij (fun (p : Fin n × Fin n) _ => (p.2, p.1))
  · intro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hp ⊢
    exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
  · intro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro ⟨i, j⟩ hp
    refine ⟨(j, i), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hp ⊢
    exact ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

/-- **Fundamental Disjoint Inversion-Count Identity**:
For disjoint `BitWord` masks `u` and `v`, the sum of the inversion counts in both orders
equals the product of their Hamming weights:
`maskInversionCount u v + maskInversionCount v u = maskWeight u * maskWeight v`. -/
theorem maskInversionCount_add_symm_of_disjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    maskInversionCount u v + maskInversionCount v u = maskWeight u * maskWeight v := by
  rw [← upperPairs_card_eq_maskInversionCount_symm u v]
  dsimp [maskInversionCount]
  rw [← Finset.card_union_of_disjoint (disjoint_maskInversionPairs_upperPairs u v)]
  rw [← activeBitProduct_eq_union_of_disjoint hdisj]
  exact activeBitProduct_card u v

private theorem sign_mul_eq_koszulSign_of_add_eq_mul (a b w₁ w₂ : ℕ)
    (h_sum : a + b = w₁ * w₂) :
    (if a % 2 = 0 then (1 : ℤ) else -1) * (if b % 2 = 0 then (1 : ℤ) else -1) =
      ChakravalaGA.koszulSign (R := ℤ)
        (if w₁ % 2 = 0 then .even else .odd)
        (if w₂ % 2 = 0 then .even else .odd) := by
  have h_mod : (a % 2 + b % 2) % 2 = ((w₁ % 2) * (w₂ % 2)) % 2 := by
    rw [← Nat.add_mod, ← Nat.mul_mod, h_sum]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one w₁ with hw₁ | hw₁ <;>
    rcases Nat.mod_two_eq_zero_or_one w₂ with hw₂ | hw₂ <;>
    simp [ha, hb, hw₁, hw₂, ChakravalaGA.koszulSign] at h_mod ⊢

/-- **Graded Koszul Sign Commutation for Disjoint BitWord Masks**:
For disjoint masks `u` and `v`, the product of their relative inversion signs equals the
ℤ₂-graded Koszul sign `(-1)^{|u| |v|}` of their Hamming weight parities. -/
theorem maskInversionSign_mul_symm_of_disjoint {n : ℕ} {u v : BitWord n}
    (hdisj : MasksDisjoint u v) :
    maskInversionSign u v * maskInversionSign v u =
      ChakravalaGA.koszulSign (R := ℤ) (maskParity u) (maskParity v) := by
  dsimp [maskInversionSign, maskParity]
  exact sign_mul_eq_koszulSign_of_add_eq_mul _ _ _ _
    (maskInversionCount_add_symm_of_disjoint hdisj)

/-- First elementary 1-blade bitmask on `Fin 2` (active at bit `0`). -/
def basisBit0 : BitWord 2 :=
  fun i => decide (i = 0)

/-- Second elementary 1-blade bitmask on `Fin 2` (active at bit `1`). -/
def basisBit1 : BitWord 2 :=
  fun i => decide (i = 1)

/-- The two elementary 1-blade bitmasks on `Fin 2` are disjoint. -/
theorem basisBit0_basisBit1_disjoint : MasksDisjoint basisBit0 basisBit1 := by
  intro i
  fin_cases i <;> decide

/-- Multiplying `basisBit0` before `basisBit1` incurs zero inversions (sign `+1`). -/
theorem maskInversionSign_basisBit0_basisBit1 :
    maskInversionSign basisBit0 basisBit1 = 1 := by
  decide

/-- Multiplying `basisBit1` before `basisBit0` incurs one inversion (sign `-1`). -/
theorem maskInversionSign_basisBit1_basisBit0 :
    maskInversionSign basisBit1 basisBit0 = -1 := by
  decide

/-!
## Archetype II: Submersion Horizontal Block Inverse, Zero Vertical Drift & Finrank Cubic Cost Reduction
-/

section SubmersionTruncation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The horizontally truncated natural gradient step `- G_H⁻¹ (projH gradL)` associated with a
`SubmersionSplit V` and horizontal block inverse operator `G_H_inv`. -/
def truncatedNaturalGradient
    (split : SubmersionSplit V) (G_H_inv : V →ₗ[ℝ] V) (gradL : V) : V :=
  - G_H_inv (split.projH gradL)

/-- When `G_H_inv` maps horizontal vectors into the horizontal subspace, the vertical projection
of `truncatedNaturalGradient` vanishes identically (`projV (Δθ) = 0`). -/
theorem truncatedNaturalGradient_projV_zero
    (split : SubmersionSplit V) (G_H_inv : V →ₗ[ℝ] V)
    (h_horiz : ∀ v, split.projV (G_H_inv (split.projH v)) = 0) (gradL : V) :
    split.projV (truncatedNaturalGradient split G_H_inv gradL) = 0 := by
  dsimp [truncatedNaturalGradient]
  rw [map_neg, h_horiz gradL, neg_zero]

/-- Under the horizontal range invariance hypothesis, `truncatedNaturalGradient` is fixed by
the horizontal projector `projH`. -/
theorem truncatedNaturalGradient_projH_eq_self
    (split : SubmersionSplit V) (G_H_inv : V →ₗ[ℝ] V)
    (h_horiz : ∀ v, split.projV (G_H_inv (split.projH v)) = 0) (gradL : V) :
    split.projH (truncatedNaturalGradient split G_H_inv gradL) =
      truncatedNaturalGradient split G_H_inv gradL :=
  horizontal_of_vertical_zero split
    (truncatedNaturalGradient split G_H_inv gradL)
    (truncatedNaturalGradient_projV_zero split G_H_inv h_horiz gradL)

/-- Under the horizontal range invariance hypothesis, `truncatedNaturalGradient` belongs to
the horizontal submodule `LinearMap.range split.projH`. -/
theorem truncatedNaturalGradient_mem_range_projH
    (split : SubmersionSplit V) (G_H_inv : V →ₗ[ℝ] V)
    (h_horiz : ∀ v, split.projV (G_H_inv (split.projH v)) = 0) (gradL : V) :
    truncatedNaturalGradient split G_H_inv gradL ∈ LinearMap.range split.projH :=
  ⟨truncatedNaturalGradient split G_H_inv gradL,
    truncatedNaturalGradient_projH_eq_self split G_H_inv h_horiz gradL⟩

/-- Canonical horizontal-sandwich linear operator `projH ∘ G_inv ∘ projH`, which restricts
any ambient linear operator `G_inv` to map into the horizontal subspace. -/
def horizontalSandwich (split : SubmersionSplit V) (G_inv : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  split.projH.comp (G_inv.comp split.projH)

/-- Any horizontal-sandwich operator `horizontalSandwich split G_inv` automatically satisfies
the zero-vertical-output condition `projV (G_H_inv (projH v)) = 0`. -/
theorem horizontalSandwich_projV_zero
    (split : SubmersionSplit V) (G_inv : V →ₗ[ℝ] V) (v : V) :
    split.projV (horizontalSandwich split G_inv (split.projH v)) = 0 := by
  dsimp [horizontalSandwich]
  exact split.orthoVH _

/-- Using `horizontalSandwich split G_inv`, the truncated natural gradient has zero vertical
component unconditionally. -/
theorem truncatedNaturalGradient_horizontalSandwich_projV_zero
    (split : SubmersionSplit V) (G_inv : V →ₗ[ℝ] V) (gradL : V) :
    split.projV (truncatedNaturalGradient split (horizontalSandwich split G_inv) gradL) = 0 :=
  truncatedNaturalGradient_projV_zero split (horizontalSandwich split G_inv)
    (horizontalSandwich_projV_zero split G_inv) gradL

/-- When `G` is a left inverse to `G_H_inv` on horizontal vectors and `gradL` is purely horizontal
(`projV gradL = 0`), `truncatedNaturalGradient` solves the exact normal equation `G (Δθ) = -gradL`. -/
theorem truncatedNaturalGradient_solves_normal_eq
    (split : SubmersionSplit V) (G G_H_inv : V →ₗ[ℝ] V)
    (h_inv : ∀ v, G (G_H_inv (split.projH v)) = split.projH v)
    (gradL : V) (h_grad_horiz : split.projV gradL = 0) :
    G (truncatedNaturalGradient split G_H_inv gradL) = - gradL := by
  dsimp [truncatedNaturalGradient]
  rw [map_neg, h_inv gradL, horizontal_of_vertical_zero split gradL h_grad_horiz]

/-- When both horizontal and vertical submersion subspaces are nontrivial, evaluating the cubic
cost model on the horizontal subspace dimension `finrank (range projH)` is strictly less than
on the ambient space dimension `finrank V`. -/
theorem truncatedNaturalGradient_finrank_cubic_cost_lt [FiniteDimensional ℝ V]
    (split : SubmersionSplit V)
    (hH : LinearMap.range split.projH ≠ ⊥)
    (hV : LinearMap.range split.projV ≠ ⊥) :
    cubicCostModel (Module.finrank ℝ (LinearMap.range split.projH)) <
      cubicCostModel (Module.finrank ℝ V) :=
  cost_horizontal_lt split hH hV

end SubmersionTruncation

/-!
## Archetype III: Chentsov Sufficient-Partition Compression & Fisher Natural Gradient Steepest Ascent Preservation
-/

section ChentsovNaturalGradient

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- The variance `Var_P(ℓ) = ∑_a P(a) ℓ(a)² - (∑_a P(a) ℓ(a))²` of a covector `ℓ` under `P`. -/
noncomputable def variance (P : ProbInterior α) (ℓ : α → ℝ) : ℝ :=
  ∑ a, P.p a * ℓ a ^ 2 - (∑ a, P.p a * ℓ a) ^ 2

/-- Pointwise evaluation of the pushed-forward interior distribution under a sufficient
statistic partition embedding `E`: `(E_* P)(b) = P(E.π b) * E.c b`. -/
theorem partitionEmbedding_pushforward_p_apply
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (b : β) :
    (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
      (partitionEmbedding_weight_pos E)).p b = P.p (E.π b) * E.c b := by
  change (pushforward (partitionEmbeddingToKernel E).kernel (toProbDist P)).p b =
    P.p (E.π b) * E.c b
  rw [congruent_pushforward_at (partitionEmbeddingToKernel E) P b]
  dsimp [partitionEmbeddingToKernel]
  simp only [↓reduceIte]

/-- Pointwise evaluation of a pushed-forward tangent vector under a sufficient statistic
partition embedding `E`: `(E_* u)(b) = u(E.π b) * E.c b`. -/
theorem partitionEmbedding_pushforwardTangentVec_apply
    (E : CongruentPartitionEmbedding α β) (u : α → ℝ) (b : β) :
    pushforwardTangentVec (partitionEmbeddingToKernel E).kernel u b =
      u (E.π b) * E.c b := by
  rw [congruent_pushforward_tangent_at (partitionEmbeddingToKernel E) u b]
  dsimp [partitionEmbeddingToKernel]
  simp only [↓reduceIte]

/-- The expectation of a lifted covector `b ↦ ℓ(E.π b)` under the pushed-forward distribution
`E_* P` equals the expectation of `ℓ` under the base distribution `P`. -/
theorem expectation_pushforward_eq
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (ℓ : α → ℝ) :
    InfoGeometry.Epistemology.FisherNaturalGradientSteepest.expectation
      (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
        (partitionEmbedding_weight_pos E))
      (fun b => ℓ (E.π b)) =
      InfoGeometry.Epistemology.FisherNaturalGradientSteepest.expectation P ℓ := by
  unfold InfoGeometry.Epistemology.FisherNaturalGradientSteepest.expectation
  calc
    ∑ b : β, (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
        (partitionEmbedding_weight_pos E)).p b * ℓ (E.π b)
      = ∑ b : β, (P.p (E.π b) * ℓ (E.π b)) * E.c b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [partitionEmbedding_pushforward_p_apply E P b]
        ring
    _ = ∑ a : α, ∑ b ∈ Finset.univ.filter (fun b : β => E.π b = a),
          (P.p (E.π b) * ℓ (E.π b)) * E.c b := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun b _ => Finset.mem_univ (E.π b))]
    _ = ∑ a : α, ∑ b ∈ Finset.univ.filter (fun b : β => E.π b = a),
          (P.p a * ℓ a) * E.c b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [hb]
    _ = ∑ a : α, (P.p a * ℓ a) *
          ∑ b ∈ Finset.univ.filter (fun b : β => E.π b = a), E.c b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum]
    _ = ∑ a : α, P.p a * ℓ a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [E.partition_sum a, mul_one]

/-- **Equivariance of the Fisher Natural Gradient under Partition Embeddings**:
Pushing the base Fisher natural gradient `fisherNaturalGradient P ℓ` forward along `E`
yields the exact Fisher natural gradient of the lifted covector `b ↦ ℓ(E.π b)` at `E_* P`. -/
theorem pushforward_fisherNaturalGradient_eq
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (ℓ : α → ℝ) :
    pushforwardTangentVec (partitionEmbeddingToKernel E).kernel
        (fisherNaturalGradient P ℓ) =
      fisherNaturalGradient
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (fun b => ℓ (E.π b)) := by
  funext b
  rw [partitionEmbedding_pushforwardTangentVec_apply E (fisherNaturalGradient P ℓ) b]
  dsimp [fisherNaturalGradient]
  rw [partitionEmbedding_pushforward_p_apply E P b, expectation_pushforward_eq E P ℓ]
  exact mul_right_comm (P.p (E.π b))
    (ℓ (E.π b) - InfoGeometry.Epistemology.FisherNaturalGradientSteepest.expectation P ℓ) (E.c b)

/-- Pushing the Fisher natural gradient and any tangent vector `w` forward along a sufficient
statistic partition embedding `E : CongruentPartitionEmbedding α β` preserves the exact
first-order differential pairing `∑_a ℓ(a) w(a)`. -/
theorem pushed_fisherNaturalGradient_pairing_eq
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (ℓ w : α → ℝ)
    (hw : ∑ a, w a = 0) :
    fisherMetric
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel (fisherNaturalGradient P ℓ))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel w) =
      ∑ a, ℓ a * w a := by
  rw [chentsov_partition_embedding_fisher_invariance E P (fisherNaturalGradient P ℓ) w]
  exact fisherMetric_naturalGradient P ℓ w hw

/-- Under any sufficient statistic partition embedding `E`, the squared Fisher norm of the
pushed-forward natural gradient equals the base variance `variance P ℓ`. -/
theorem pushed_fisherNaturalGradient_norm_sq_eq_variance
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (ℓ : α → ℝ) :
    fisherMetric
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel (fisherNaturalGradient P ℓ))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel (fisherNaturalGradient P ℓ)) =
      variance P ℓ := by
  rw [chentsov_partition_embedding_fisher_invariance E P
    (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ)]
  rw [← fisherNaturalGradient_rate_eq_norm_sq P ℓ]
  exact fisherNaturalGradient_rate_eq_variance P ℓ

/-- **Chentsov-Invariant Steepest Ascent**:
If a tangent vector `w` has pushed-forward Fisher norm squared at `E_* P` at most that of the
pushed-forward natural gradient, its first-order ascent rate `∑_a ℓ(a) w(a)` is bounded above
by the natural-gradient ascent rate `∑_a ℓ(a) n(a)`. -/
theorem pushed_fisherNaturalGradient_steepest_ascent
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (ℓ w : α → ℝ)
    (hw : ∑ a, w a = 0)
    (hlen : fisherMetric
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel w)
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel w) ≤
      fisherMetric
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel (fisherNaturalGradient P ℓ))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel (fisherNaturalGradient P ℓ))) :
    ∑ a, ℓ a * w a ≤ ∑ a, ℓ a * fisherNaturalGradient P ℓ a := by
  have hlen_base :
      fisherMetric P w w ≤
        fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ) := by
    rw [← chentsov_partition_embedding_fisher_invariance E P w w,
      ← chentsov_partition_embedding_fisher_invariance E P
        (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ)]
    exact hlen
  exact fisherNaturalGradient_steepest_ascent P ℓ w hw hlen_base

end ChentsovNaturalGradient

/-!
## Archetype IV: Safe KV-Cache Attention Sink Floor Renormalization & GNS Anchor Faithfulness
-/

section SinkFloorRenormalization

variable {ι : Type*}

/-- Unnormalized attention weights after enforcing a positive lower floor `m` at the `anchor` token. -/
def flooredWeights [DecidableEq ι] (w : ι → ℝ) (anchor : ι) (m : ℝ) (i : ι) : ℝ :=
  if i = anchor then max (w anchor) m else w i

/-- Renormalized attention sink distribution obtained by dividing `flooredWeights` by its sum. -/
noncomputable def renormalizedSinkWeights [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (anchor : ι) (m : ℝ) (i : ι) : ℝ :=
  flooredWeights w anchor m i / ∑ k, flooredWeights w anchor m k

/-- Non-negativity of `flooredWeights` when `w` is non-negative and the floor `m` is positive. -/
theorem flooredWeights_nonneg [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) (i : ι) :
    0 ≤ flooredWeights w anchor m i := by
  dsimp [flooredWeights]
  split_ifs with h
  · exact le_trans (le_of_lt hm) (le_max_right (w anchor) m)
  · exact hw i

/-- At `anchor`, the floored weight is bounded below by the floor `m`. -/
theorem flooredWeights_anchor_ge_floor [DecidableEq ι]
    (w : ι → ℝ) (anchor : ι) (m : ℝ) :
    m ≤ flooredWeights w anchor m anchor := by
  dsimp [flooredWeights]
  simp only [↓reduceIte]
  exact le_max_right (w anchor) m

/-- Pointwise upper bound on `flooredWeights`: each floored weight is at most `w i` plus the
anchor floor increment `if i = anchor then m else 0`. -/
theorem flooredWeights_le_add_ite [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) (i : ι) :
    flooredWeights w anchor m i ≤ w i + (if i = anchor then m else 0) := by
  dsimp [flooredWeights]
  have hm_nonneg : 0 ≤ m := le_of_lt hm
  have hw_i : 0 ≤ w i := hw i
  split_ifs with h
  · subst h
    exact max_le (le_add_of_nonneg_right hm_nonneg) (le_add_of_nonneg_left hw_i)
  · rw [add_zero]

/-- When the original weights `w` sum to `1`, the total mass of `flooredWeights` is bounded
above by `1 + m`. -/
theorem flooredWeights_sum_le_one_add [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (anchor : ι) {m : ℝ} (hm : 0 < m) :
    ∑ i, flooredWeights w anchor m i ≤ 1 + m := by
  calc
    ∑ i, flooredWeights w anchor m i
      ≤ ∑ i, (w i + (if i = anchor then m else 0)) :=
        Finset.sum_le_sum (fun i _ => flooredWeights_le_add_ite hw anchor hm i)
    _ = (∑ i, w i) + ∑ i, (if i = anchor then m else 0) :=
        Finset.sum_add_distrib
    _ = 1 + m := by
        rw [hsum, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ↓reduceIte]

/-- The total mass of `flooredWeights` is strictly positive whenever `w ≥ 0` and `m > 0`. -/
theorem flooredWeights_sum_pos [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) :
    0 < ∑ k, flooredWeights w anchor m k := by
  have h_anchor_pos : 0 < flooredWeights w anchor m anchor :=
    lt_of_lt_of_le hm (flooredWeights_anchor_ge_floor w anchor m)
  exact Finset.sum_pos'
    (fun k _ => flooredWeights_nonneg hw anchor hm k)
    ⟨anchor, Finset.mem_univ anchor, h_anchor_pos⟩

/-- Every renormalized sink weight is non-negative. -/
theorem renormalizedSinkWeights_nonneg [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) (i : ι) :
    0 ≤ renormalizedSinkWeights w anchor m i := by
  dsimp [renormalizedSinkWeights]
  exact div_nonneg
    (flooredWeights_nonneg hw anchor hm i)
    (le_of_lt (flooredWeights_sum_pos hw anchor hm))

/-- The renormalized sink weights sum to `1`. -/
theorem renormalizedSinkWeights_sum_one [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) :
    ∑ i, renormalizedSinkWeights w anchor m i = 1 := by
  dsimp [renormalizedSinkWeights]
  have h_den_ne : (∑ k, flooredWeights w anchor m k) ≠ 0 :=
    ne_of_gt (flooredWeights_sum_pos hw anchor hm)
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  exact div_self h_den_ne

/-- The renormalized sink weight at `anchor` is strictly positive (`> 0`). -/
theorem renormalizedSinkWeights_anchor_pos [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m) :
    0 < renormalizedSinkWeights w anchor m anchor := by
  dsimp [renormalizedSinkWeights]
  have h_num : 0 < flooredWeights w anchor m anchor :=
    lt_of_lt_of_le hm (flooredWeights_anchor_ge_floor w anchor m)
  exact div_pos h_num (flooredWeights_sum_pos hw anchor hm)

/-- Explicit quantitative lower bound on the renormalized anchor weight: when `w ≥ 0` sums to `1`,
enforcing floor `m > 0` guarantees `m / (1 + m) ≤ renormalizedSinkWeights w anchor m anchor`. -/
theorem renormalizedSinkWeights_anchor_ge_div_one_add [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (anchor : ι) {m : ℝ} (hm : 0 < m) :
    m / (1 + m) ≤ renormalizedSinkWeights w anchor m anchor := by
  dsimp [renormalizedSinkWeights]
  exact le_trans
    (div_le_div_of_nonneg_left (le_of_lt hm)
      (flooredWeights_sum_pos hw anchor hm)
      (flooredWeights_sum_le_one_add hw hsum anchor hm))
    (div_le_div_of_nonneg_right
      (flooredWeights_anchor_ge_floor w anchor m)
      (le_of_lt (flooredWeights_sum_pos hw anchor hm)))

/-- Quantitative GNS quadratic lower bound: the diagonal GNS inner product `<A, A>_ρ` under
`renormalizedSinkWeights` is bounded below by the anchor weight times the squared norm of the
anchor column of `A`. -/
theorem renormalizedSinkWeights_gns_anchor_lower_bound [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor : ι) {m : ℝ} (hm : 0 < m)
    (A : Matrix ι ι ℝ) :
    renormalizedSinkWeights w anchor m anchor * (∑ j, (A j anchor) ^ 2) ≤
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (Matrix.diagonal (renormalizedSinkWeights w anchor m)) A A := by
  rw [InfoGeometry.QuantumContext.MatrixGNS.gnsInner_self_diagonal]
  refine Finset.single_le_sum
    (f := fun i => renormalizedSinkWeights w anchor m i * (∑ j, (A j i) ^ 2))
    (fun i _ => ?_) (Finset.mem_univ anchor)
  exact mul_nonneg
    (renormalizedSinkWeights_nonneg hw anchor hm i)
    (Finset.sum_nonneg (fun j _ => sq_nonneg (A j i)))

/-- Explicit floor-parameterized GNS quadratic lower bound: when `w ≥ 0` sums to `1`, the
diagonal GNS inner product `<A, A>_ρ` under `renormalizedSinkWeights` is bounded below by
`(m / (1 + m)) * ∑ j, (A j anchor)²`. -/
theorem renormalizedSinkWeights_gns_anchor_ge_div_one_add [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (anchor : ι) {m : ℝ} (hm : 0 < m) (A : Matrix ι ι ℝ) :
    (m / (1 + m)) * (∑ j, (A j anchor) ^ 2) ≤
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (Matrix.diagonal (renormalizedSinkWeights w anchor m)) A A := by
  refine le_trans ?_ (renormalizedSinkWeights_gns_anchor_lower_bound hw anchor hm A)
  exact mul_le_mul_of_nonneg_right
    (renormalizedSinkWeights_anchor_ge_div_one_add hw hsum anchor hm)
    (Finset.sum_nonneg (fun j _ => sq_nonneg (A j anchor)))

/-- Anchor-column GNS faithfulness: any matrix observable `A` with a non-zero entry `A j anchor ≠ 0`
in the anchor column has strictly positive GNS energy `<A, A>_ρ > 0` under `renormalizedSinkWeights`. -/
theorem renormalizedSinkWeights_gns_anchor_separating [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (anchor j : ι) {m : ℝ} (hm : 0 < m)
    (A : Matrix ι ι ℝ) (h_nz : A j anchor ≠ 0) :
    0 < InfoGeometry.QuantumContext.MatrixGNS.gnsInner
      (Matrix.diagonal (renormalizedSinkWeights w anchor m)) A A := by
  have h_col_pos : 0 < ∑ k, (A k anchor) ^ 2 :=
    Finset.sum_pos' (fun k _ => sq_nonneg (A k anchor))
      ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero h_nz⟩
  have h_prod_pos :
      0 < renormalizedSinkWeights w anchor m anchor * (∑ k, (A k anchor) ^ 2) :=
    mul_pos (renormalizedSinkWeights_anchor_pos hw anchor hm) h_col_pos
  exact lt_of_lt_of_le h_prod_pos
    (renormalizedSinkWeights_gns_anchor_lower_bound hw anchor hm A)

end SinkFloorRenormalization

end InfoGeometry.Export.DualEngineCertifiedContracts
