import Mathlib
import InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological
import InfoGeometry.Topology.Conf3DeRhamCandidateTopological

/-!
# `Conf₃` braid-shadow / de Rham product packet

This file packages the already-verified `Conf₃` braid-shadow readout together
with the existing de Rham candidate packet.  It only records the product
chart and its coordinate projections.  It does not identify the braid-shadow
carrier with the de Rham candidate carrier.
-/

namespace InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopological

noncomputable section

/-- Finite triples normalized to `0,1,∞` on the product-chart side. -/
abbrev Conf3FiniteTriple :=
  InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological.FiniteTriple

/-- The combined `Conf₃` braid-shadow / de Rham candidate packet. -/
abbrev Conf3ArnoldDeRhamProductPacket (R : Type*) [CommRing R] (D : ℕ) :=
  InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.Conf3ArnoldBraidShadowPacket R ×
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.Conf3DeRhamCandidatePacket D

instance conf3ArnoldDeRhamProductPacketTopologicalSpace
    (R : Type*) [CommRing R] (D : ℕ) :
    TopologicalSpace (Conf3ArnoldDeRhamProductPacket R D) := ⊥

instance conf3ArnoldDeRhamProductPacketDiscreteTopology
    (R : Type*) [CommRing R] (D : ℕ) :
    DiscreteTopology (Conf3ArnoldDeRhamProductPacket R D) := ⟨rfl⟩

/-- The canonical product packet built from a normalized finite triple and a
de Rham candidate branch. -/
def conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    Conf3ArnoldDeRhamProductPacket R D :=
  (InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
      (R := R) p,
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
      D p data)

@[simp] theorem conf3ArnoldDeRhamProductPacketOf_fst
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).1 =
      InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
        (R := R) p := by
  rfl

@[simp] theorem conf3ArnoldDeRhamProductPacketOf_snd
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2 =
      InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data := by
  rfl

/-- The combined product packet is continuous because the topology is discrete. -/
theorem continuous_conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommRing R] (D : ℕ) :
    Continuous (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D)) := by
  exact continuous_of_discreteTopology

/-- The combined product packet is locally constant because the topology is
discrete. -/
theorem isLocallyConstant_conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommRing R] (D : ℕ) :
    IsLocallyConstant (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D)) := by
  exact IsLocallyConstant.of_discrete
    (f := conf3ArnoldDeRhamProductPacketOf (R := R) (D := D))

/-- The braid-shadow component readout. -/
def conf3ArnoldDeRhamProductBraidShadow
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.Conf3ArnoldBraidShadowPacket R :=
  (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).1

/-- The de Rham candidate component readout. -/
def conf3ArnoldDeRhamProductDeRhamCandidate
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.Conf3DeRhamCandidatePacket D :=
  (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2

@[simp] theorem conf3ArnoldDeRhamProductBraidShadow_eq
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    conf3ArnoldDeRhamProductBraidShadow (R := R) (D := D) p data =
      InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
        (R := R) p := by
  rfl

@[simp] theorem conf3ArnoldDeRhamProductDeRhamCandidate_eq
    (R : Type*) [CommRing R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    conf3ArnoldDeRhamProductDeRhamCandidate (R := R) (D := D) p data =
      InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data := by
  rfl

end
