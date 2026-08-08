import Mathlib
import InfoGeometry.Projective.ArnoldRelations
import InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological
import InfoGeometry.Topology.AmplituhedronBoundaryRank32

/-!
# Configuration-space normalization and Arnold readout

This is a small topological packet for the `Conf₃` normalization story.
It couples the already-proved `0, 1, ∞` Möbius normalization property with the
canonical three-edge Arnold relation carrier.  The file does **not** claim an
analytic de Rham computation or a Feynman period evaluation.
-/

namespace InfoGeometry.Topology.Conf3ArnoldNormalizationTopological

open InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological
open InfoGeometry.Topology.AmplituhedronBoundary
open InfoGeometry.Projective.ArnoldRelations
open InfoGeometry.Projective.Amplituhedron

noncomputable section

variable {R : Type*} [CommRing R]

/-- The combined `Conf₃` normalization / Arnold carrier packet. -/
abbrev Conf3ArnoldPacket (R : Type*) [CommRing R] :=
  (MobiusTransform × RiemannSphere × RiemannSphere × RiemannSphere) ×
    ThreePointArnoldExterior R

instance conf3ArnoldPacketTopologicalSpace (R : Type*) [CommRing R] :
    TopologicalSpace (Conf3ArnoldPacket R) := ⊥

instance conf3ArnoldPacketDiscreteTopology (R : Type*) [CommRing R] :
    DiscreteTopology (Conf3ArnoldPacket R) := ⟨rfl⟩

/-- The canonical Arnold mixed relation for the three-point channel. -/
def conf3ArnoldMixedRelation : ThreePointArnoldExterior R :=
  arnoldMixedRelation R (EdgeModule R (Fin 3))
    (w R (Fin 3) 0 1)
    (w R (Fin 3) 1 2)
    (w R (Fin 3) 2 0)

/-- The combined normalization packet for a finite triple. -/
def conf3ArnoldNormalizationPacket (p : FiniteTriple) : Conf3ArnoldPacket R :=
  (finiteTripleNormalizationPacket p, conf3ArnoldMixedRelation (R := R))

@[simp] theorem conf3ArnoldNormalizationPacket_fst (p : FiniteTriple) :
    (conf3ArnoldNormalizationPacket (R := R) p).1 =
      finiteTripleNormalizationPacket p := by
  rfl

@[simp] theorem conf3ArnoldNormalizationPacket_snd (p : FiniteTriple) :
    (conf3ArnoldNormalizationPacket (R := R) p).2 =
      conf3ArnoldMixedRelation (R := R) := by
  rfl

/-- The canonical Arnold mixed relation vanishes in the Arnold quotient. -/
theorem conf3ArnoldMixedRelation_quotient_zero :
    (RingQuot.mkRingHom (ArnoldRel R (Fin 3)))
      (conf3ArnoldMixedRelation (R := R)) = 0 := by
  simpa [conf3ArnoldMixedRelation, arnoldMixedRelation] using
    (arnold_mixed_relation_quotient_zero (R := R) (ι := Fin 3) 0 1 2)

/-- The packet is continuous because we install the discrete topology. -/
theorem continuous_conf3ArnoldNormalizationPacket :
    Continuous (conf3ArnoldNormalizationPacket (R := R)) := by
  exact continuous_of_discreteTopology

/-- The packet is locally constant because we install the discrete topology. -/
theorem isLocallyConstant_conf3ArnoldNormalizationPacket :
    IsLocallyConstant (conf3ArnoldNormalizationPacket (R := R)) := by
  exact IsLocallyConstant.of_discrete
    (f := conf3ArnoldNormalizationPacket (R := R))

end

