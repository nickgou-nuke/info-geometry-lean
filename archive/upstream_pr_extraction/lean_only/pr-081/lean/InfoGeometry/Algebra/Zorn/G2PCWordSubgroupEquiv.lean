import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

/-!
# The canonical finite carrier for the concrete unipotent subgroup

The subgroup is defined by the range of the six-bit PC normal form.  This
owner exposes that range as an actual equivalence, keeping the CAS and Lean
unipotent carriers identical.
-/

namespace InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv

open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable instance : Fintype unipotentSubgroup := Fintype.ofFinite _

def pcWordSubtype (e : PCWordExp) : unipotentSubgroup :=
  ⟨pcWord e, ⟨e, rfl⟩⟩

theorem pcWordSubtype_injective :
    Function.Injective pcWordSubtype := by
  intro e f h
  apply G2TwoPCRecovery.pcWord_injective
  exact congrArg Subtype.val h

theorem pcWordSubtype_surjective :
    Function.Surjective pcWordSubtype := by
  intro x
  rcases x.property with ⟨e, he⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  exact he

noncomputable def pcWordEquivUnipotent :
    PCWordExp ≃ unipotentSubgroup :=
  Equiv.ofBijective pcWordSubtype
    ⟨pcWordSubtype_injective, pcWordSubtype_surjective⟩

theorem unipotent_card_eq_pcWordExp :
    Fintype.card unipotentSubgroup = Fintype.card PCWordExp := by
  exact Fintype.card_congr pcWordEquivUnipotent.symm

theorem unipotent_fintype_card :
    Fintype.card unipotentSubgroup = 64 := by
  rw [unipotent_card_eq_pcWordExp]
  exact G2TwoSylowSubgroup.pcWordExp_card

end InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv
