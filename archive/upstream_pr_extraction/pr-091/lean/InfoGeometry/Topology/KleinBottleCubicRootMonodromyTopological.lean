import Mathlib
import InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

/-!
# Topological family of cubic Klein-bottle charges

The chiral Klein-bottle charge is parameterized by the actual subtype of
cube roots of unity.  The family is given the discrete root topology, while
the finite linear-operator target is also discrete.  The conjugation law is
reused directly from the canonical owner.
-/

namespace InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

open InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

noncomputable section

abbrev CubicRootParameter := {w : ℂ // w ^ 3 = 1}
abbrev ColourFiber :=
  InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.A2ColourFiber ℂ
abbrev ColourOperator := ColourFiber →ₗ[ℂ] ColourFiber

instance cubicRootParameterTopologicalSpace :
    TopologicalSpace CubicRootParameter := ⊥

instance cubicRootParameterDiscreteTopology :
    DiscreteTopology CubicRootParameter := ⟨rfl⟩

instance colourOperatorTopologicalSpace :
    TopologicalSpace ColourOperator := ⊥

instance colourOperatorDiscreteTopology :
    DiscreteTopology ColourOperator := ⟨rfl⟩

/-- Cubic charge as a continuous family over the root parameter. -/
def cubicRootChargeReadout (q : CubicRootParameter) : ColourOperator :=
  InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge q.1

@[simp] theorem cubicRootChargeReadout_apply (q : CubicRootParameter) :
    cubicRootChargeReadout q =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge q.1 := by
  rfl

theorem continuous_cubicRootChargeReadout :
    Continuous cubicRootChargeReadout := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_cubicRootChargeReadout :
    IsLocallyConstant cubicRootChargeReadout := by
  exact IsLocallyConstant.of_discrete (f := cubicRootChargeReadout)

/-- Every member of the family has order three. -/
theorem cubicRootChargeReadout_cube (q : CubicRootParameter) :
    (cubicRootChargeReadout q).comp
        ((cubicRootChargeReadout q).comp (cubicRootChargeReadout q)) =
      LinearMap.id := by
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge_cube
    q.1 q.2

/-- The fixed reflection reverses every cubic charge in the family. -/
theorem chiralExchange_conj_cubicRootChargeReadout
    (q : CubicRootParameter) :
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
      (K := ℂ)).comp
        ((cubicRootChargeReadout q).comp
          (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
            (K := ℂ))) =
      (cubicRootChargeReadout q).comp (cubicRootChargeReadout q) := by
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_conj_cubicCharge
    q.1 q.2

end
end InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
