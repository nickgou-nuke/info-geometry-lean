import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological
import InfoGeometry.Topology.Conf3DeRhamCandidateTopological

/-!
# `Conf₃` braid-shadow / de Rham product packet

This file packages the already-verified `Conf₃` braid-shadow readout together
with the existing de Rham candidate packet.  It only records the product
chart and its coordinate projections.  It does not identify the braid-shadow
carrier with the de Rham candidate carrier.

#### BUCKET 1: CLOSED FINITE THEOREMS
The product packet retains the input triple and branch data, and its branch
rank readouts are transported from the de Rham candidate owner.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The ranks `32` and `24` require their corresponding `relationChoice` proofs.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic de Rham computation or non-discrete geometric continuity result
is asserted by this product chart.
-/

namespace InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopological

noncomputable section

/-- Finite triples normalized to `0,1,∞` on the product-chart side. -/
abbrev Conf3FiniteTriple :=
  InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological.FiniteTriple

/-- The combined `Conf₃` braid-shadow / de Rham candidate packet. -/
abbrev Conf3ArnoldDeRhamProductPacket (R : Type*) [CommSemiring R] (D : ℕ) :=
  InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.Conf3ArnoldBraidShadowPacket R ×
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.Conf3DeRhamCandidatePacket D

instance conf3ArnoldDeRhamProductPacketTopologicalSpace
    (R : Type*) [CommSemiring R] (D : ℕ) :
    TopologicalSpace (Conf3ArnoldDeRhamProductPacket R D) := ⊥

instance conf3ArnoldDeRhamProductPacketDiscreteTopology
    (R : Type*) [CommSemiring R] (D : ℕ) :
    DiscreteTopology (Conf3ArnoldDeRhamProductPacket R D) := ⟨rfl⟩

/-- The canonical product packet built from a normalized finite triple and a
de Rham candidate branch. -/
def conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    Conf3ArnoldDeRhamProductPacket R D :=
  (InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
      (R := R) p,
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
      D p data)

@[simp] theorem conf3ArnoldDeRhamProductPacketOf_fst
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).1 =
      InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
        (R := R) p := by
  rfl

@[simp] theorem conf3ArnoldDeRhamProductPacketOf_snd
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2 =
      InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data := by
  rfl

/-- The combined product packet is continuous because the topology is discrete. -/
theorem continuous_conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommSemiring R] (D : ℕ) :
    Continuous (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D)) := by
  rw [continuous_def]
  intro s hs
  exact isOpen_discrete _

/-- The combined product packet is locally constant because the topology is
discrete. -/
theorem isLocallyConstant_conf3ArnoldDeRhamProductPacketOf
    (R : Type*) [CommSemiring R] (D : ℕ) :
    IsLocallyConstant (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D)) := by
  exact IsLocallyConstant.of_discrete
    (f := conf3ArnoldDeRhamProductPacketOf (R := R) (D := D))

/-- The braid-shadow component readout. -/
def conf3ArnoldDeRhamProductBraidShadow
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.Conf3ArnoldBraidShadowPacket R :=
  (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).1

/-- The de Rham candidate component readout. -/
def conf3ArnoldDeRhamProductDeRhamCandidate
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.Conf3DeRhamCandidatePacket D :=
  (conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2

@[simp] theorem conf3ArnoldDeRhamProductBraidShadow_eq
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    conf3ArnoldDeRhamProductBraidShadow (R := R) (D := D) p data =
      InfoGeometry.Topology.Conf3ArnoldBraidShadowTopological.conf3ArnoldBraidShadowPacketOf
        (R := R) p := by
  rfl

@[simp] theorem conf3ArnoldDeRhamProductDeRhamCandidate_eq
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    conf3ArnoldDeRhamProductDeRhamCandidate (R := R) (D := D) p data =
      InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data := by
  rfl

/-! ## Faithfulness and branch readouts of the product packet -/

/-- Equality of product packets recovers both the normalized triple and its
finite de Rham branch data, since the second component is the source pair. -/
theorem conf3ArnoldDeRhamProductPacketOf_eq_iff
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p₁ p₂ : Conf3FiniteTriple)
    (data₁ data₂ : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p₁ data₁ =
        conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p₂ data₂ ↔
      p₁ = p₂ ∧ data₁ = data₂ := by
  constructor
  · intro h
    have hdata := congrArg Prod.snd h
    change (p₁, data₁) = (p₂, data₂) at hdata
    exact Prod.mk.inj hdata
  · rintro ⟨rfl, rfl⟩
    rfl

/-- On the product/Leray branch, the combined packet's de Rham readout has
rank `32`; the result is read from the actual second component. -/
theorem conf3ArnoldDeRhamProductPacketOf_product_rank
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D)
    (hchoice : data.relationChoice =
      NonIsoConf3DeRhamCooperad.ModelChoice.productLeray) :
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank D
      ((conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2) = 32 := by
  change InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank D
      (InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data) = 32
  exact InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank_product
    D (InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
      D p data) hchoice

/-- On the Orlik--Solomon alpha branch, the combined packet's de Rham readout
has rank `24`. -/
theorem conf3ArnoldDeRhamProductPacketOf_osAlpha_rank
    (R : Type*) [CommSemiring R] (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D)
    (hchoice : data.relationChoice =
      NonIsoConf3DeRhamCooperad.ModelChoice.osAlpha) :
    InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank D
      ((conf3ArnoldDeRhamProductPacketOf (R := R) (D := D) p data).2) = 24 := by
  change InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank D
      (InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
        D p data) = 24
  exact InfoGeometry.Topology.Conf3DeRhamCandidateTopological.conf3DeRhamBranchRank_os
    D (InfoGeometry.Topology.Conf3DeRhamCandidateTopological.normalizedConf3DeRhamPacket
      D p data) hchoice

end
end InfoGeometry.Topology.Conf3ArnoldDeRhamProductTopological
