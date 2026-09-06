import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Basic
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
# Reduction of the ambient group order to the coset-space cardinality

This module reduces the long-standing blocker

  `Nat.card SplitOctF2Aut = 12096`

to a single remaining native obligation: constructing a bijection
`Fin 189 ≃ (SplitOctF2Aut ⧸ sylowTwoSubgroup)` (equivalently, proving the
parabolic coset space has cardinality 189).

Established natively here:

1. `sylowTwoSubgroup_card_nat` / `sylowTwoSubgroup_card_fin`:
   `card sylowTwoSubgroup = 64`, derived from the existing
   `unipotentSubgroup_card` and `sylowTwoSubgroup_eq_unipotentSubgroup`
   in `G2TwoPCSubgroupClosure`.
2. `nat_card_eq_of_quotient_189`: given ANY proof that the quotient has 189
   elements, the ambient order follows from mathlib's
   `Subgroup.card_eq_card_quotient_mul_card_subgroup`.
3. `card_eq_of_equiv_189`: the same reduction phrased against the exact
   residual interface `Fin 189 ≃ Quotient`.
4. `sylowTwoSubgroupOfCardOfQuotient`: under the quotient hypothesis,
   the existing conditional interface `sylowTwoSubgroupOfCard`
   (`G2BNBruhatFramework`) becomes constructible.

All proofs are complete, kernel-checked, and carry no unproved placeholders.
-/

namespace InfoGeometry.Algebra.Zorn.G2GroupOrderReduction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable instance : Fintype (↥G2TwoSylowSubgroup.sylowTwoSubgroup) := by
  classical
  exact Fintype.subtype
    ((Finset.univ : Finset SplitOctF2Aut).filter
      (fun x => x ∈ G2TwoSylowSubgroup.sylowTwoSubgroup)) (by
        intro x
        simp)

/-- The certified cardinality of the unipotent/Sylow candidate subgroup: 64. -/
theorem sylowTwoSubgroup_card_nat :
    Nat.card G2TwoSylowSubgroup.sylowTwoSubgroup = 64 := by
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
  exact InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup_card

/-- Finite-cardinality form of the same fact. -/
theorem sylowTwoSubgroup_card_fin :
    Fintype.card G2TwoSylowSubgroup.sylowTwoSubgroup = 64 := by
  rw [← Nat.card_eq_fintype_card]
  exact sylowTwoSubgroup_card_nat

/-- **Reduction theorem**: if the parabolic coset space `G ⧸ U` has exactly
189 elements, then the ambient automorphism group has order `189 * 64 = 12096`. -/
theorem nat_card_eq_of_quotient_189
    (hq : Nat.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) = 189) :
    Nat.card SplitOctF2Aut = 12096 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    hq, sylowTwoSubgroup_card_nat]

/-- **Residual interface**: an explicit bijection `Fin 189 ≃ G ⧸ U` yields
the quotient cardinality, hence the ambient order via the reduction theorem. -/
theorem nat_card_eq_of_equiv_189
    (e : Fin 189 ≃ (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup)) :
    Nat.card SplitOctF2Aut = 12096 := by
  letI : Fintype (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) :=
    Fintype.ofEquiv (Fin 189) e
  have hq : Nat.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) = 189 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) =
          Fintype.card (Fin 189) := (Fintype.card_congr e).symm
      _ = 189 := Fintype.card_fin 189
  exact nat_card_eq_of_quotient_189 hq

/-- Under the quotient hypothesis, the existing conditional interface
`sylowTwoSubgroupOfCard` from `G2BNBruhatFramework` becomes constructible. -/
noncomputable def sylowTwoSubgroupOfCardOfQuotient
    (hq : Nat.card (SplitOctF2Aut ⧸ G2TwoSylowSubgroup.sylowTwoSubgroup) = 189) :
    Sylow 2 SplitOctF2Aut :=
  InfoGeometry.Algebra.Zorn.G2BNBruhatFramework.sylowTwoSubgroupOfCard
    (nat_card_eq_of_quotient_189 hq)

end InfoGeometry.Algebra.Zorn.G2GroupOrderReduction
