import InfoGeometry.Algebra.Zorn.G2WeylGroupEquiv

/-!
# Completed finite Weyl-group carrier for `G₂`

The parameter type `ZMod 6 × Bool` is a normal-form index, not a group
definition.  The group carrier is the concrete subgroup of split-octonion
automorphisms.  This file packages the already proved coverage and
injectivity into the final carrier-level statements, without introducing a
second multiplication law on the parameter type.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

theorem weylNF_range_eq_weylG2Subgroup :
    Set.range (fun p : WeylG2 => weylNF p.1 p.2) =
      weylG2Subgroup.carrier := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact weylNF_mem_weylG2Subgroup p.1 p.2
  · intro hx
    obtain ⟨p, hp⟩ := weylG2Subgroup_coverage_pair ⟨x, hx⟩
    exact ⟨p, hp.symm⟩

noncomputable def weylG2ParameterEquiv_is_group_carrier :
    WeylG2 ≃ weylG2Subgroup :=
  weylG2ParameterEquiv

theorem weylG2ParameterEquiv_surjective :
    Function.Surjective (weylG2ParameterEquiv) :=
  weylG2ParameterEquiv.surjective

theorem weylG2ParameterEquiv_injective :
    Function.Injective (weylG2ParameterEquiv) :=
  weylG2ParameterEquiv.injective

theorem weylG2_concrete_group_card :
    Fintype.card weylG2Subgroup = Fintype.card WeylG2 := by
  exact (weylG2ParameterEquiv_card).symm

theorem weylG2_concrete_group_card_eq_twelve :
    Fintype.card weylG2Subgroup = 12 := by
  rw [← weylG2_card]
  exact weylG2_concrete_group_card

end InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
