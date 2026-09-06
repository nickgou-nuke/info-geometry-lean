import Mathlib
import InfoGeometry.Topology.Conf3ArnoldNormalizationTopological
import InfoGeometry.Topology.ArtinBraidS3Quotient

/-!
# Configuration-space Arnold braid shadow

This packet packages the normalized Conf₃ Arnold carrier together with the
concrete `B₃ → S₃` Artin quotient shadow already proved in the topology layer.
It is only a topological readout and discrete packaging.  It does not claim an
analytic monodromy theorem or a new configuration-space comparison.
-/

namespace InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological

open InfoGeometry.Topology.Conf3ArnoldNormalizationTopological
open InfoGeometry.Topology.ArtinBraidS3Quotient

noncomputable section

variable {R : Type*} [CommRing R]
abbrev Conf3FiniteTriple :=
  InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological.FiniteTriple

/-- The combined Conf₃ Arnold packet and braid shadow packet. -/
abbrev Conf3ArnoldBraidShadowPacket (R : Type*) [CommRing R] :=
  InfoGeometry.Topology.Conf3ArnoldNormalizationTopological.Conf3ArnoldPacket R ×
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))

instance conf3ArnoldBraidShadowPacketTopologicalSpace (R : Type*) [CommRing R] :
    TopologicalSpace (Conf3ArnoldBraidShadowPacket R) := ⊥

instance conf3ArnoldBraidShadowPacketDiscreteTopology (R : Type*) [CommRing R] :
    DiscreteTopology (Conf3ArnoldBraidShadowPacket R) := ⟨rfl⟩

/-- The canonical braid shadow packet uses the adjacent transpositions in `S₃`. -/
def conf3ArnoldBraidShadowPacketOf (p : Conf3FiniteTriple) :
    Conf3ArnoldBraidShadowPacket R :=
  (InfoGeometry.Topology.Conf3ArnoldNormalizationTopological.conf3ArnoldNormalizationPacket
      (R := R) p,
    (InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1,
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2))

@[simp] theorem conf3ArnoldBraidShadowPacket_fst (p : Conf3FiniteTriple) :
    (conf3ArnoldBraidShadowPacketOf (R := R) p).1 =
      InfoGeometry.Topology.Conf3ArnoldNormalizationTopological.conf3ArnoldNormalizationPacket
        (R := R) p := by
  rfl

@[simp] theorem conf3ArnoldBraidShadowPacket_snd_fst (p : Conf3FiniteTriple) :
    (conf3ArnoldBraidShadowPacketOf (R := R) p).2.1 =
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 := by
  rfl

@[simp] theorem conf3ArnoldBraidShadowPacket_snd_snd (p : Conf3FiniteTriple) :
    (conf3ArnoldBraidShadowPacketOf (R := R) p).2.2 =
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 := by
  rfl

/-- The packet is continuous because the topology is discrete. -/
theorem continuous_conf3ArnoldBraidShadowPacketOf :
    Continuous (conf3ArnoldBraidShadowPacketOf (R := R)) := by
  exact continuous_of_discreteTopology

/-- The packet is locally constant because the topology is discrete. -/
theorem isLocallyConstant_conf3ArnoldBraidShadowPacketOf :
    IsLocallyConstant (conf3ArnoldBraidShadowPacketOf (R := R)) := by
  exact IsLocallyConstant.of_discrete
    (f := conf3ArnoldBraidShadowPacketOf (R := R))

/-- The braid shadow satisfies the concrete `B₃` Artin relation. -/
theorem conf3ArnoldBraidShadow_artin_relation :
    InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 =
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.s3_adjacent_artin_relation

/-- The first braid generator squares to the identity. -/
theorem conf3ArnoldBraidShadow_sigma1_sq :
    InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 = 1 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1_sq

/-- The second braid generator squares to the identity. -/
theorem conf3ArnoldBraidShadow_sigma2_sq :
    InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 = 1 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2_sq

end

end InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological
