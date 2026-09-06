import Mathlib
import InfoGeometry.Canonical.KleinBottleCyclotomicChiralLift

/-!
# Topological readout of the cyclotomic chiral lift

The canonical owner supplies the finite-dimensional linear operators and
their relations.  This file adds only the explicitly discrete topology and
continuity/local-constancy readouts; it does not introduce a new operator
system or an analytic completion.
-/

namespace InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

open InfoGeometry.Canonical

noncomputable section

variable {K : Type*} [Field K]

abbrev A2ColourFiber (K : Type*) := InfoGeometry.Canonical.A2ColourFiber K

instance a2ColourFiberTopologicalSpace : TopologicalSpace (A2ColourFiber K) := ⊥
instance a2ColourFiberDiscreteTopology : DiscreteTopology (A2ColourFiber K) := ⟨rfl⟩

def cubicCharge (w : K) : A2ColourFiber K →ₗ[K] A2ColourFiber K :=
  InfoGeometry.Canonical.kleinCubicCharge w

def chiralExchange : A2ColourFiber K →ₗ[K] A2ColourFiber K :=
  InfoGeometry.Canonical.chiralExchange

theorem cubicCharge_cube (w : K) (hw : w ^ 3 = 1) :
    (cubicCharge w).comp ((cubicCharge w).comp (cubicCharge w)) =
      LinearMap.id := by
  exact InfoGeometry.Canonical.kleinCubicCharge_cube w hw

theorem chiralExchange_square :
    (@chiralExchange K _).comp (@chiralExchange K _) =
      LinearMap.id := by
  exact InfoGeometry.Canonical.chiralExchange_square (K := K)

theorem chiralExchange_conj_cubicCharge (w : K) (hw : w ^ 3 = 1) :
    (@chiralExchange K _).comp
        ((cubicCharge w).comp (@chiralExchange K _)) =
      (cubicCharge w).comp (cubicCharge w) := by
  exact InfoGeometry.Canonical.chiralExchange_conj_kleinCubicCharge w hw

theorem continuous_cubicCharge (w : K) :
    Continuous (cubicCharge w) := continuous_of_discreteTopology

theorem continuous_chiralExchange :
    Continuous (@chiralExchange K _ ) := continuous_of_discreteTopology

theorem isLocallyConstant_cubicCharge (w : K) :
    IsLocallyConstant (cubicCharge w) :=
  IsLocallyConstant.of_discrete _

theorem isLocallyConstant_chiralExchange :
    IsLocallyConstant (@chiralExchange K _ ) :=
  IsLocallyConstant.of_discrete _

end
end InfoGeometry.Topology.KleinBottleCyclotomicChiralLift
