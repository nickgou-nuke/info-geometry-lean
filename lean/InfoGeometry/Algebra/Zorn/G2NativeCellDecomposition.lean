/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedBruhatCover
import InfoGeometry.Algebra.Zorn.G2SignatureCellSeparation
import InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

/-! Native disjoint-cell decomposition and ambient generation. -/
namespace InfoGeometry.Algebra.Zorn.G2NativeCellDecomposition

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2TwoBruhatClassification G2QuotientOrbitSeparation
open G2ConcreteWeylG2 G2TwoPCSubgroupClosure G2TwoSylowSubgroup
open G2ConcreteGeneratorInfrastructure

theorem exists_unique_cell (g : SplitOctF2Aut) :
    ∃! k : Fin 12, g ∈ concreteBruhatCell (orbitWeylRepresentative k) := by
  obtain ⟨p, hp⟩ := concreteBruhatCoverObligation_iff_covering_eq_univ.mpr
    G2CorrectedBruhatCover.concrete_cover g
  obtain ⟨k, hk⟩ := G2TitsRepresentativeInjectivity.orbitWeyl_bijective.2 p
  have hg : g ∈ concreteBruhatCell (orbitWeylRepresentative k) := by
    simpa [orbitWeylRepresentative, hk] using hp
  refine ⟨k, hg, ?_⟩
  intro l hl
  by_contra h
  exact Set.disjoint_left.mp (G2SignatureCellSeparation.cells_disjoint h) hl hg

/-- Forgetting the cell index is a bijection, not only a covering map. -/
theorem forget_cell_bijective : Function.Bijective
    (fun x : (Σ k : Fin 12, concreteBruhatCell (orbitWeylRepresentative k)) =>
      (x.2 : SplitOctF2Aut)) := by
  constructor
  · rintro ⟨i, g, hg⟩ ⟨j, h, hh⟩ heq
    change g = h at heq
    subst h
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (G2SignatureCellSeparation.cells_disjoint hne) hg hh
    subst j
    rfl
  · intro g
    obtain ⟨k, hk, _⟩ := exists_unique_cell g
    exact ⟨⟨k, g, hk⟩, rfl⟩

/-- Explicit carrier equivalence for the native twelve-cell partition. -/
noncomputable def cellDecomposition :
    (Σ k : Fin 12, concreteBruhatCell (orbitWeylRepresentative k)) ≃ SplitOctF2Aut :=
  Equiv.ofBijective _ forget_cell_bijective

theorem weyl_mem_BN_generators (p : WeylG2) :
    weylNF p.1 p.2 ∈ concreteBNGeneratorSubgroup := by
  have hs : s ∈ concreteBNGeneratorSubgroup :=
    Subgroup.subset_closure (Or.inr (by simp))
  have ht : t ∈ concreteBNGeneratorSubgroup :=
    Subgroup.subset_closure (Or.inr (by simp))
  have hc : c ∈ concreteBNGeneratorSubgroup := by
    have h := concreteBNGeneratorSubgroup.mul_mem hs ht
    simpa [t, ← mul_assoc, s_sq] using h
  cases hb : p.2 <;>
    simp only [weylNF]
  · exact concreteBNGeneratorSubgroup.pow_mem hc _
  · exact concreteBNGeneratorSubgroup.mul_mem hs
      (concreteBNGeneratorSubgroup.pow_mem hc _)

theorem BN_generators_eq_top : concreteBNGeneratorSubgroup = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨p, a, b, ha, hb, rfl⟩ :=
    concreteBruhatCoverObligation_iff_covering_eq_univ.mpr
      G2CorrectedBruhatCover.concrete_cover g
  rw [sylowTwoSubgroup_eq_unipotentSubgroup] at ha hb
  exact concreteBNGeneratorSubgroup.mul_mem
    (concreteBNGeneratorSubgroup.mul_mem
      (Subgroup.subset_closure (Or.inl ha)) (weyl_mem_BN_generators p))
    (Subgroup.subset_closure (Or.inl hb))

end InfoGeometry.Algebra.Zorn.G2NativeCellDecomposition
