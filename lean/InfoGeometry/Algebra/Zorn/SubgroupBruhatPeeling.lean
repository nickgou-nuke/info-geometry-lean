/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.BruhatPeelingTransport
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Peeling restricted to a subgroup, retaining an actual subword witness. -/
namespace InfoGeometry.Algebra.Zorn.BruhatPeeling

variable {G : Type*} [Group G]

theorem subgroup_word_peeling (B N : Subgroup G) (S : Set G)
    (hSN : S ⊆ N)
    (hstep : ∀ r ∈ S, ∀ n ∈ N, ∀ x, InCell B x n →
      InCell B (r * x) n ∨ InCell B (r * x) (r * n))
    (L : List G) (hL : ∀ r ∈ L, r ∈ S)
    {n x : G} (hn : n ∈ N) (hx : InCell B x n) :
    ∃ K : List G, K.Sublist L ∧ InCell B (L.prod * x) (K.prod * n) := by
  induction L with
  | nil =>
      exact ⟨[], List.Sublist.refl [], by simpa using hx⟩
  | cons r L ih =>
      have hr : r ∈ S := hL r (by simp)
      have htail : ∀ t ∈ L, t ∈ S := fun t ht => hL t (List.mem_cons_of_mem r ht)
      obtain ⟨K, hK, hxK⟩ := ih htail
      have hKN : K.prod * n ∈ N :=
        N.mul_mem (N.list_prod_mem (fun t ht => hSN (htail t (hK.subset ht)))) hn
      rcases hstep r hr _ hKN _ hxK with h | h
      · refine ⟨K, hK.cons r, ?_⟩
        simpa only [List.prod_cons, mul_assoc] using h
      · refine ⟨r :: K, hK.cons_cons r, ?_⟩
        simpa only [List.prod_cons, mul_assoc] using h

end InfoGeometry.Algebra.Zorn.BruhatPeeling
