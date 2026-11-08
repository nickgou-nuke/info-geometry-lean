import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2GroupOrderReduction

/-!
# Native conditional orbit-membership assembly

This owner packages the explicit hypotheses needed to turn the 189-word
quotient enumeration into a concrete twelve-cell cover. The orbit-membership
premise is intentionally explicit: the word table and its partition do not by
themselves prove that every word lies in the claimed quotient orbit.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate

open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev CarrierQuotient :=
  SplitOctF2Aut ⧸
    InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup

theorem covering_eq_univ
    (enum : Fin 189 ≃ CarrierQuotient)
    (p : Fin 12 → WeylG2)
    (cells : Fin 12 → Finset (Fin 189))
    (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ cells k →
      ∃ b : SplitOctF2Aut,
        b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup ∧
          enum i = b •
            (QuotientGroup.mk (weylNF (p k).1 (p k).2) : CarrierQuotient))
    (hpartition : Finset.univ.biUnion cells = Finset.univ) :
    concreteBruhatCovering = Set.univ := by
  exact concreteBruhatCovering_eq_univ_of_fin189_orbit_partition
    enum p cells hcell hpartition

theorem quotient_card (enum : Fin 189 ≃ CarrierQuotient) :
    Nat.card CarrierQuotient = 189 := by
  simpa using (Nat.card_congr enum).symm

theorem ambient_order (enum : Fin 189 ≃ CarrierQuotient) :
    Nat.card SplitOctF2Aut = 12096 := by
  apply InfoGeometry.Algebra.Zorn.G2GroupOrderReduction.nat_card_eq_of_quotient_189
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
  exact quotient_card enum

end InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
