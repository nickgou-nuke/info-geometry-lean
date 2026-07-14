import CanonicalZornOuterTrialityGroup

/-!
# Spin/related-triples representation fiber

Mathlib defines `spinGroup Q` inside the Clifford algebra and the canonical
Zorn construction supplies its Dirac representation on `8s ⊕ 8c`.  The
related-triples group independently acts on `8v`, `8s`, and `8c`.

This file forms their exact fiber product over the Dirac general linear
group.  An element is a spin element together with a related triple whose
two semispinor components give the same Dirac operator.  This is the honest
group-level bridge available before proving that every spin element admits a
unique related triple (the classical triality identification).
-/

noncomputable section

namespace CanonicalZornSpinRelatedFiber

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornOuterTrialityGroup

abbrev ComplexSpin44 := spinGroup vectorQuadratic
abbrev DiracGL := LinearMap.GeneralLinearGroup ℂ DiracSpinor16

/-- Block-diagonal Dirac action of the two semispinor components of a
related triple. -/
def relatedDiracRepresentation : CartanTrialityGroup →* DiracGL where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.prodCongr g.1.2.1.toLinearEquiv g.1.2.2.toLinearEquiv)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro Ψ
    rfl
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro Ψ
    rfl

theorem relatedDiracRepresentation_apply
    (g : CartanTrialityGroup) (S : SpinorPlus8) (C : SpinorMinus8) :
    ((relatedDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, C) =
      (spinorPlusAct g.1.2.1 S, spinorMinusAct g.1.2.2 C) := by
  rfl

/-- Predicate saying that a spin element and a related triple induce exactly
the same operator on the Dirac carrier. -/
def SpinRelatedCompatible
    (p : ComplexSpin44 × CartanTrialityGroup) : Prop :=
  complexSpinDiracRepresentation p.1 = relatedDiracRepresentation p.2

/-- Fiber product of the complex spin group and the related-triples group
over their Dirac representations. -/
def spinRelatedFiber : Subgroup (ComplexSpin44 × CartanTrialityGroup) where
  carrier := {p | SpinRelatedCompatible p}
  one_mem' := by
    simp [SpinRelatedCompatible]
  mul_mem' := by
    intro g h hg hh
    change complexSpinDiracRepresentation g.1 =
      relatedDiracRepresentation g.2 at hg
    change complexSpinDiracRepresentation h.1 =
      relatedDiracRepresentation h.2 at hh
    change complexSpinDiracRepresentation (g.1 * h.1) =
      relatedDiracRepresentation (g.2 * h.2)
    rw [map_mul, map_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change complexSpinDiracRepresentation g.1 =
      relatedDiracRepresentation g.2 at hg
    change complexSpinDiracRepresentation g.1⁻¹ =
      relatedDiracRepresentation g.2⁻¹
    rw [map_inv, map_inv, hg]

/-- The group of compatible spin/related-triple pairs. -/
abbrev SpinRelatedFiber := spinRelatedFiber

/-- Projection of the compatibility fiber to Mathlib's spin group. -/
def toSpin : SpinRelatedFiber →* ComplexSpin44 where
  toFun g := g.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the compatibility fiber to the related-triples group. -/
def toRelatedTriple : SpinRelatedFiber →* CartanTrialityGroup where
  toFun g := g.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fiber_representation_eq (g : SpinRelatedFiber) :
    complexSpinDiracRepresentation (toSpin g) =
      relatedDiracRepresentation (toRelatedTriple g) :=
  g.2

/-- Operator-level form of compatibility: the Clifford spin action is the
pair of semispinor actions carried by the related triple. -/
theorem fiber_dirac_action
    (g : SpinRelatedFiber) (S : SpinorPlus8) (C : SpinorMinus8) :
    ((complexSpinDiracRepresentation (toSpin g) : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, C) =
      (spinorPlusAct (toRelatedTriple g).1.2.1 S,
        spinorMinusAct (toRelatedTriple g).1.2.2 C) := by
  rw [fiber_representation_eq]
  exact relatedDiracRepresentation_apply _ _ _

/-- The compatibility fiber is nonempty: both identity transformations form
the canonical base point. -/
def spinRelatedIdentity : SpinRelatedFiber := ⟨(1, 1), by
  change complexSpinDiracRepresentation 1 = relatedDiracRepresentation 1
  rw [map_one, map_one]⟩

@[simp] theorem toSpin_identity : toSpin spinRelatedIdentity = 1 := rfl

@[simp] theorem toRelatedTriple_identity :
    toRelatedTriple spinRelatedIdentity = 1 := rfl

/-- The fiber product, its two projections, and agreement of the induced
Dirac actions form one compiler-visible group-level bridge. -/
theorem spin_related_triality_group_bridge (g : SpinRelatedFiber)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    SpinRelatedCompatible ((toSpin g), (toRelatedTriple g)) ∧
    ((complexSpinDiracRepresentation (toSpin g) : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, C) =
      (spinorPlusAct (toRelatedTriple g).1.2.1 S,
        spinorMinusAct (toRelatedTriple g).1.2.2 C) := by
  exact ⟨fiber_representation_eq g, fiber_dirac_action g S C⟩

end CanonicalZornSpinRelatedFiber

end noncomputable section
