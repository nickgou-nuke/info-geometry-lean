import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Sylow
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

namespace InfoGeometry.Algebra.Zorn.G2GroupOrderReduction

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem sylowTwoSubgroup_card_nat :
    Nat.card (G2TwoSylowSubgroup.sylowTwoSubgroup : Subgroup SplitOctF2Aut) = 64 := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
  exact InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup_card

theorem nat_card_eq_of_quotient_189
    (hq : Nat.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) = 189) :
    Nat.card SplitOctF2Aut = 12096 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hq,
    sylowTwoSubgroup_card_nat]

theorem nat_card_eq_of_equiv_189
    (e : Fin 189 ≃
      (SplitOctF2Aut ⧸ (G2TwoSylowSubgroup.sylowTwoSubgroup : Subgroup SplitOctF2Aut))) :
    Nat.card SplitOctF2Aut = 12096 := by
  apply nat_card_eq_of_quotient_189
  rw [← Nat.card_congr e]
  simp

noncomputable def sylowTwoSubgroupOfCardOfQuotient
    (hq : Nat.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) = 189) :
    Sylow 2 SplitOctF2Aut := by
  apply InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.sylowTwoSubgroupOfCard
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hq,
    sylowTwoSubgroup_card_nat]

end InfoGeometry.Algebra.Zorn.G2GroupOrderReduction
