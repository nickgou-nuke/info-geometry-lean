import InfoGeometry.Algebra.Zorn.G2BruhatResidualNormalForm
import InfoGeometry.Algebra.Zorn.G2GroupOrderReduction

/-!
# The Weyl-only `fullPeel` target is incompatible with the ambient order

The PC recovery factorization writes every carrier element as a product of a
64-element PC factor and `fullPeel`.  If the latter were always one of the 12
Weyl representatives, the carrier would inject into a set of cardinality
`64 * 12`.  Consequently the unconditional Weyl-membership statement is not
the missing classification theorem: under the already identified ambient
order it is false.
-/

namespace InfoGeometry.Algebra.Zorn.G2FullPeelWeylObstruction

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2GroupOrderReduction

noncomputable def fullPeelWeylCoordinates
    (h : ∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup)
    (f : SplitOctF2Aut) : ZMod 6 × Bool :=
  Classical.choose (show ∃ p : ZMod 6 × Bool,
      fullPeel f = weylNF p.1 p.2 from by
    rcases weylG2Subgroup_coverage (fullPeel f) (h f) with ⟨k, b, hk⟩
    exact ⟨(k, b), hk⟩)

theorem fullPeelWeylCoordinates_spec
    (h : ∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup)
    (f : SplitOctF2Aut) :
    fullPeel f = weylNF (fullPeelWeylCoordinates h f).1
      (fullPeelWeylCoordinates h f).2 := by
  exact Classical.choose_spec (show ∃ p : ZMod 6 × Bool,
      fullPeel f = weylNF p.1 p.2 from by
    rcases weylG2Subgroup_coverage (fullPeel f) (h f) with ⟨k, b, hk⟩
    exact ⟨(k, b), hk⟩)

noncomputable def fullPeelWeylEncoding
    (h : ∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup) :
    SplitOctF2Aut →
      G2TwoSylowSubgroup.sylowTwoSubgroup × (ZMod 6 × Bool) :=
  fun f =>
    (⟨pcWord (extractAllBits f), pcWord_mem_sylow _⟩,
      fullPeelWeylCoordinates h f)

theorem fullPeelWeylEncoding_injective
    (h : ∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup) :
    Function.Injective (fullPeelWeylEncoding h) := by
  intro f g hfg
  have hq : pcWord (extractAllBits f) = pcWord (extractAllBits g) := by
    have hq' := congrArg Prod.fst hfg
    exact congrArg Subtype.val hq'
  have hp : fullPeelWeylCoordinates h f = fullPeelWeylCoordinates h g := by
    exact congrArg Prod.snd hfg
  have hnf : fullPeel f = fullPeel g := by
    rw [fullPeelWeylCoordinates_spec h f, fullPeelWeylCoordinates_spec h g, hp]
  have hf : pcWord (extractAllBits f) * fullPeel f = f := by
    exact fullPeel_pcWord_factorization f
  have hg : pcWord (extractAllBits g) * fullPeel g = g := by
    exact fullPeel_pcWord_factorization g
  rw [← hf, ← hg, hq, hnf]

theorem not_fullPeel_mem_weylG2Subgroup_of_ambient_card
    (hG : Nat.card SplitOctF2Aut = 12096) :
    ¬ (∀ f : SplitOctF2Aut, fullPeel f ∈ weylG2Subgroup) := by
  intro h
  have hcard : Nat.card SplitOctF2Aut ≤
      Nat.card (G2TwoSylowSubgroup.sylowTwoSubgroup × (ZMod 6 × Bool)) := by
    rw [Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective _ (fullPeelWeylEncoding_injective h)
  rw [hG, Nat.card_prod, sylowTwoSubgroup_card_nat] at hcard
  norm_num [Nat.card_eq_fintype_card, ZMod.card] at hcard

end InfoGeometry.Algebra.Zorn.G2FullPeelWeylObstruction
