/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.AttentionPolytope
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Support-preserving compression of a fixed attention readout

The output is a list of distinct original key indices with positive weights,
not merely a small set of points in value space. Only keys having positive
original mass may be selected. Mathlib owns the Carathéodory argument.
The support depends on the row and fixed values; no future-query or gradient
preservation is asserted, and this existence proof is not executable extraction.
-/

namespace InfoGeometry.Routing.AttentionPolytope
open scoped BigOperators

variable {m d : ℕ}

/-- Zero-weight keys can be excluded from the convex-hull carrier. -/
theorem readout_mem_convexHull_positive_support (p : Fin m → ℝ)
    (V : Fin m → Fin d → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    (∑ j, p j • V j) ∈ convexHull ℝ (V '' {j | 0 < p j}) := by
  classical
  let s := Finset.univ.filter (fun j => p j ≠ 0)
  have hs' : ∑ j ∈ s, p j = 1 := by
    simpa only [s, Finset.sum_filter_ne_zero] using hs
  have hv : ∑ j ∈ s, p j • V j = ∑ j, p j • V j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : p j = 0 := by simpa [s] using hj
    simp [hz]
  rw [← hv]
  apply (convex_convexHull ℝ _).sum_mem (fun j _ => hp j) hs'
  intro j hj
  apply subset_convexHull ℝ _
  exact ⟨j, lt_of_le_of_ne (hp j) (Ne.symm (Finset.mem_filter.mp hj).2), rfl⟩

/-- A fixed readout admits at most `d+1` distinct, originally supported keys.
The retained values are affinely independent and all retained weights positive. -/
theorem exists_sparse_key_readout (p : Fin m → ℝ) (V : Fin m → Fin d → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) :
    ∃ r : ℕ, r ≤ d + 1 ∧ ∃ key : Fin r ↪ Fin m, ∃ w : Fin r → ℝ,
      (∀ i, 0 < p (key i)) ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i = 1) ∧ (∑ i, w i • V (key i) = ∑ j, p j • V j) ∧
      AffineIndependent ℝ (fun i => V (key i)) := by
  classical
  obtain ⟨ι, hι, z, w, hz, ha, hw, hsum, hread⟩ :=
    eq_pos_convex_span_of_mem_convexHull
      (readout_mem_convexHull_positive_support p V hp hs)
  let := hι
  have hchoice (i : ι) : ∃ j, 0 < p j ∧ V j = z i := hz (Set.mem_range_self i)
  choose key hpos hval using hchoice
  have hinj : Function.Injective key := by
    intro i j hij
    apply ha.injective
    rw [← hval i, ← hval j, hij]
  let e := (Fintype.equivFin ι).symm
  have hcard : Fintype.card ι ≤ d + 1 := by
    have h := ha.card_le_finrank_succ
    have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    have hvdim : Module.finrank ℝ (Fin d → ℝ) = d := by simp
    omega
  refine ⟨Fintype.card ι, hcard, ⟨key ∘ e, hinj.comp e.injective⟩,
    w ∘ e, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hpos (e i)
  · exact fun i => hw (e i)
  · simpa only [Function.comp_apply] using (e.sum_comp w).trans hsum
  · change (∑ i, w (e i) • V (key (e i))) = _
    simp_rw [hval]
    exact (e.sum_comp (fun i => w i • z i)).trans hread
  · change AffineIndependent ℝ (fun i => V (key (e i)))
    simp_rw [hval]
    exact ha.comp_embedding e.toEmbedding

/-- Compress every row on its original support, preserving the complete matrix
readout. Different queries may retain different keys. -/
theorem exists_sparse_attention_readout {n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : A ∈ attentionPolytope n m)
    (V : Matrix (Fin m) (Fin d) ℝ) :
    ∃ Q : Matrix (Fin n) (Fin m) ℝ,
      Q ∈ attentionPolytope n m ∧
      (∀ i j, A i j = 0 → Q i j = 0) ∧
      (∀ i, (Finset.univ.filter (fun j => Q i j ≠ 0)).card ≤ d + 1) ∧
      Q * V = A * V := by
  classical
  choose r hr key w hpos hw hmass hread ha using
    fun i => exists_sparse_key_readout (A i) V (hA.1 i) (hA.2 i)
  let Q : Matrix (Fin n) (Fin m) ℝ :=
    fun i j => ∑ t, if key i t = j then w i t else 0
  have hnonneg (i j) : 0 ≤ Q i j := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact (hw i t).le
    · exact le_refl 0
  have hsum (i) : ∑ j, Q i j = 1 := by
    dsimp [Q]
    rw [Finset.sum_comm]
    simpa using hmass i
  have hzero (i j) (hz : A i j = 0) : Q i j = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have hne : key i t ≠ j := by
      intro he
      have ht := hpos i t
      rw [he, hz] at ht
      exact (lt_irrefl 0) ht
    simp [hne]
  have hcard (i) : (Finset.univ.filter (fun j => Q i j ≠ 0)).card ≤ d + 1 := by
    have hsub : Finset.univ.filter (fun j => Q i j ≠ 0) ⊆
        Finset.univ.image (key i) := by
      intro j hj
      by_contra hn
      apply (Finset.mem_filter.mp hj).2
      apply Finset.sum_eq_zero
      intro t _
      have hne : key i t ≠ j := by
        intro he
        exact hn (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, he⟩)
      simp [hne]
    exact (Finset.card_le_card hsub).trans
      (Finset.card_image_le.trans (by simpa using hr i))
  have hreadQ (i) : (∑ j, Q i j • V j) = ∑ j, A i j • V j := by
    dsimp [Q]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    simpa only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] using hread i
  refine ⟨Q, ⟨hnonneg, hsum⟩, hzero, hcard, ?_⟩
  ext i c
  simpa [Matrix.mul_apply, Finset.sum_apply] using congrFun (hreadQ i) c

end InfoGeometry.Routing.AttentionPolytope
