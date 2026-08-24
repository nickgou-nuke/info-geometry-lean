import InfoGeometry.Algebra.Zorn.G2GAPCosetHomomorphismBridge
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-!
# Native quotient action for the concrete carrier

This is the carrier-side action on the quotient by the verified PC subgroup.
It does not assume a finite quotient cardinality or a GAP enumeration.
-/

namespace InfoGeometry.Algebra.Zorn.G2CarrierQuotientAction

open InfoGeometry.Algebra.Zorn.G2GAPQuotientBridge
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev BorelQuotient := SplitOctF2Aut ⧸ unipotentSubgroup

def act (g : SplitOctF2Aut) : BorelQuotient → BorelQuotient :=
  cosetAction unipotentSubgroup g

@[simp] theorem act_mk (g x : SplitOctF2Aut) :
    act g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) := by
  rfl

theorem act_one (c : BorelQuotient) : act 1 c = c := by
  exact cosetAction_one unipotentSubgroup c

theorem act_mul (g h : SplitOctF2Aut) (c : BorelQuotient) :
    act (g * h) c = act g (act h c) := by
  exact cosetAction_mul unipotentSubgroup g h c

theorem base_stabilizer (g : SplitOctF2Aut) :
    act g (QuotientGroup.mk 1 : BorelQuotient) = QuotientGroup.mk 1 ↔
      g ∈ unipotentSubgroup := by
  change QuotientGroup.mk (g * 1) = QuotientGroup.mk 1 ↔
    g ∈ unipotentSubgroup
  rw [QuotientGroup.eq]
  constructor
  · intro h
    exact unipotentSubgroup.inv_mem h
  · intro h
    exact unipotentSubgroup.inv_mem h

end InfoGeometry.Algebra.Zorn.G2CarrierQuotientAction
