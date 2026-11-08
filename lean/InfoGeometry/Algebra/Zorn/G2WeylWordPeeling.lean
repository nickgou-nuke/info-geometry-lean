/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.SubgroupBruhatPeeling
import InfoGeometry.Algebra.Zorn.G2TwoCellTransition

/-! Native corrected-generator word peeling with a subword certificate. -/
namespace InfoGeometry.Algebra.Zorn.G2WeylWordPeeling

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2ConcreteWeylG2 G2ConcreteBN2CorrectSecondConjugation
open G2TwoBruhatClassification G2TwoPCSubgroupClosure

theorem corrected_reflections_mem_weyl :
    ({s, correctedT} : Set SplitOctF2Aut) ⊆ weylG2Subgroup := by
  intro r hr
  rcases hr with rfl | hr
  · exact s_mem_weylG2Subgroup
  · have heq : r = correctedT := hr
    rw [heq, correctedT, concreteWeylElement_eleven_eq_weylNF_five_true]
    exact weylNF_mem_weylG2Subgroup 5 true

theorem two_cell_on_weyl {r n g : SplitOctF2Aut}
    (hr : r ∈ ({s, correctedT} : Set SplitOctF2Aut))
    (hn : n ∈ weylG2Subgroup) (hg : g ∈ concreteBruhatCell n) :
    r * g ∈ concreteBruhatCell n ∨ r * g ∈ concreteBruhatCell (r * n) := by
  obtain ⟨p, hp⟩ := weylG2Subgroup_coverage_pair ⟨n, hn⟩
  change n = weylNF p.1 p.2 at hp
  rw [hp] at hg ⊢
  exact G2TwoCellTransition.corrected_two_cell_transition hr p hg

theorem word_peeling (L : List SplitOctF2Aut)
    (hL : ∀ r ∈ L, r ∈ ({s, correctedT} : Set SplitOctF2Aut))
    {n g : SplitOctF2Aut} (hn : n ∈ weylG2Subgroup)
    (hg : g ∈ concreteBruhatCell n) :
    ∃ K : List SplitOctF2Aut, K.Sublist L ∧
      L.prod * g ∈ concreteBruhatCell (K.prod * n) := by
  have hcell (x w : SplitOctF2Aut) :
      x ∈ concreteBruhatCell w ↔ BruhatPeeling.InCell unipotentSubgroup x w := by
    rw [concreteBruhatCell_eq_exact_unipotentCell]
    rfl
  obtain ⟨K, hK, h⟩ := BruhatPeeling.subgroup_word_peeling
    unipotentSubgroup weylG2Subgroup {s, correctedT}
    corrected_reflections_mem_weyl
    (fun r hr n hn x hx => by
      rcases two_cell_on_weyl hr hn ((hcell x n).mpr hx) with h | h
      · exact Or.inl ((hcell _ _).mp h)
      · exact Or.inr ((hcell _ _).mp h))
    L hL hn ((hcell g n).mp hg)
  exact ⟨K, hK, (hcell _ _).mpr h⟩

end InfoGeometry.Algebra.Zorn.G2WeylWordPeeling
