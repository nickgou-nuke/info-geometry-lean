import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots

/-!
# Native residual form for the concrete Bruhat cells

The refined Bruhat normal form has a right residual factor.  It is therefore
not correct to require `fullPeel f` itself to be a Weyl representative.  This
owner exposes the residual factor directly through the existing concrete cell
and peel theorems.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualNormalForm

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-! The pure-Weyl residual statement is conditional: membership in the
concrete Weyl subgroup is the missing classification theorem, not an
algebraic consequence of the six PC peel coordinates. -/

theorem fullPeel_eq_weylNF_of_mem_weylG2Subgroup
    (f : SplitOctF2Aut)
    (hf : fullPeel f ∈ weylG2Subgroup) :
    ∃ k : ZMod 6, ∃ b : Bool, fullPeel f = weylNF k b := by
  exact weylG2Subgroup_coverage (fullPeel f) hf

theorem fullPeel_pc_factorization_of_mem_weylG2Subgroup
    (f : SplitOctF2Aut)
    (hf : fullPeel f ∈ weylG2Subgroup) :
    ∃ e : PCWordExp, ∃ k : ZMod 6, ∃ b : Bool,
      f = G2TwoSylowSubgroup.pcWord e * weylNF k b := by
  obtain ⟨k, b, hres⟩ :=
    fullPeel_eq_weylNF_of_mem_weylG2Subgroup f hf
  obtain ⟨e, he⟩ := factorization_of_fullPeel_eq_weyl f k b hres
  exact ⟨e, k, b, he⟩

theorem fullPeel_weyl_residual_specification :
    (∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup) →
      ∀ f : SplitOctF2Aut, ∃ k : ZMod 6, ∃ b : Bool,
        fullPeel f = weylNF k b := by
  intro h f
  exact fullPeel_eq_weylNF_of_mem_weylG2Subgroup f (h f)

theorem fullPeel_has_right_residual
    (f : SplitOctF2Aut) (p : WeylG2)
    (hf : f ∈ concreteBruhatCell (weylNF p.1 p.2)) :
    ∃ b₁ b₂ : SplitOctF2Aut,
      b₁ ∈ sylowTwoSubgroup ∧ b₂ ∈ sylowTwoSubgroup ∧
        fullPeel f = b₁ * weylNF p.1 p.2 * b₂ := by
  have hcell : fullPeel f ∈ concreteBruhatCell (weylNF p.1 p.2) :=
    fullPeel_mem_same_concreteBruhatCell hf
  exact hcell

/-- A concrete Bruhat cover gives the correct unconditional residual shape for
`fullPeel`: the remaining factor stays in a Borel double coset.  This is the
native replacement for the false claim that `fullPeel f` is itself Weyl. -/
theorem fullPeel_has_right_residual_of_cover
    (hcover : concreteBruhatCoverObligation)
    (f : SplitOctF2Aut) :
    ∃ p : WeylG2, ∃ b₁ b₂ : SplitOctF2Aut,
      b₁ ∈ sylowTwoSubgroup ∧ b₂ ∈ sylowTwoSubgroup ∧
        fullPeel f = b₁ * weylNF p.1 p.2 * b₂ := by
  obtain ⟨p, hf⟩ := hcover f
  obtain ⟨b₁, b₂, hb₁, hb₂, hres⟩ :=
    fullPeel_has_right_residual f p hf
  exact ⟨p, b₁, b₂, hb₁, hb₂, hres⟩

end InfoGeometry.Algebra.Zorn.G2BruhatResidualNormalForm
