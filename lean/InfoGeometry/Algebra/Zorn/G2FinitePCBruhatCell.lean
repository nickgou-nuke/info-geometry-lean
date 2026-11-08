import InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ConcreteCarrierDecidableEq
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# Finite PC-word presentation of a concrete Bruhat cell

The CAS and Lean use the same ordered six-bit `PCWordExp` carrier.  This
owner packages the two-sided PC normal form as a finite set, while retaining
the existing set-theoretic Bruhat-cell definition as the semantic owner.
-/

set_option maxRecDepth 100000
namespace InfoGeometry.Algebra.Zorn.G2FinitePCBruhatCell

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv

def pcBruhatCell (w : SplitOctF2Aut) : Finset SplitOctF2Aut :=
  Finset.univ.biUnion fun e : PCWordExp =>
    Finset.univ.image fun f : PCWordExp => pcWord e * w * pcWord f

theorem mem_pcBruhatCell_iff (w g : SplitOctF2Aut) :
    g ∈ pcBruhatCell w ↔ g ∈ concreteBruhatCell w := by
  constructor
  · intro hg
    simp only [pcBruhatCell, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hg
    rcases hg with ⟨e, f, rfl⟩
    exact ⟨pcWord e, pcWord f, pcWord_mem_sylow e,
      pcWord_mem_sylow f, rfl⟩
  · intro hg
    rcases hg with ⟨b₁, b₂, hb₁, hb₂, hEq⟩
    have hu₁ : b₁ ∈ G2TwoPCSubgroupClosure.unipotentSubgroup := by
      rw [← G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
      exact hb₁
    have hu₂ : b₂ ∈ G2TwoPCSubgroupClosure.unipotentSubgroup := by
      rw [← G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
      exact hb₂
    obtain ⟨e, he⟩ := pcWordSubtype_surjective ⟨b₁, hu₁⟩
    obtain ⟨f, hf⟩ := pcWordSubtype_surjective ⟨b₂, hu₂⟩
    simp only [pcBruhatCell, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    refine ⟨e, f, ?_⟩
    change pcWord e * w * pcWord f = g
    have he' : pcWord e = b₁ := congrArg Subtype.val he
    have hf' : pcWord f = b₂ := congrArg Subtype.val hf
    rw [he', hf', hEq]

end InfoGeometry.Algebra.Zorn.G2FinitePCBruhatCell
