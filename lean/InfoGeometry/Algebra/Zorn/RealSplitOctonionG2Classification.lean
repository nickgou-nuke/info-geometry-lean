import InfoGeometry.Algebra.Zorn.G2TwoSplitZorn
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger

/-!
# Real split-octonion `G₂` classification boundary

This module separates two different meanings that are easy to conflate:

* finite `G₂(2)`: the Chevalley/Atlas group over `F₂`, order `12096`;
* real split `G₂`: the real Lie group of type `G₂` acting on split octonions,
  often written `G_{2(2)}` in real-form notation.

The requested real classification is theorem-honest only when an explicit real
split `G₂` group carrier and a certificate of its action on the real Zorn
split-octonion owner are supplied.  This file therefore provides exact readbacks
from the existing `ClassificationCertificate` surface and exact finite/evidence
ledger readbacks.  It does not identify the real split Lie group with the finite
Chevalley group.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.RealSplitOctonionG2Classification

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.G2TwoSplitZorn
open InfoGeometry.Algebra.Zorn.SplitOctonionG2ClassificationCertificate

/-- Compatibility carrier for the finite/root-system evidence owner.

The carrier is the imported `G2EvidenceInvariants`; this module no longer
duplicates a second evidence structure or stores raw numerical markers. -/
abbrev RealSplitBoundaryEvidence := G2EvidenceInvariants

namespace RealSplitBoundaryEvidence

abbrev finiteAtlasG2TwoOrder (e : RealSplitBoundaryEvidence) : ℕ :=
  e.atlasG2TwoOrder

abbrev finiteDerivedOrder (_e : RealSplitBoundaryEvidence) : ℕ :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger.g2TwoDerivedOrder

abbrev pgl3F3Order (_e : RealSplitBoundaryEvidence) : ℕ :=
  InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger.pgl3F3Order

abbrev realSplitLieDimension (e : RealSplitBoundaryEvidence) : ℕ :=
  e.derivationDimension

end RealSplitBoundaryEvidence

/-- Evidence readback from the imported finite/root-system owner. -/
abbrev realSplitBoundaryEvidence : RealSplitBoundaryEvidence :=
  computationalEvidenceInvariants

/-- Exact evidence readback for the finite/real-boundary ledger. -/
theorem realSplitBoundaryEvidence_packet :
    realSplitBoundaryEvidence.finiteAtlasG2TwoOrder = 12096 ∧
      realSplitBoundaryEvidence.finiteDerivedOrder = 6048 ∧
      realSplitBoundaryEvidence.pgl3F3Order = 5616 ∧
      realSplitBoundaryEvidence.realSplitLieDimension = 14 ∧
      realSplitBoundaryEvidence.rootCount = 12 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The finite Atlas `G₂(2)` order agrees with the finite split-Zorn ledger. -/
theorem finiteAtlasG2TwoOrder_eq_lean_g2twoOrder :
    realSplitBoundaryEvidence.finiteAtlasG2TwoOrder =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.g2twoOrder := by
  exact rfl

/-- The `PGL₃(3)` order is not the finite `G₂(2)` order. -/
theorem pgl3F3Order_ne_finiteAtlasG2TwoOrder :
    realSplitBoundaryEvidence.pgl3F3Order ≠
      realSplitBoundaryEvidence.finiteAtlasG2TwoOrder := by
  exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger.pgl3F3Order_ne_g2TwoOrder

variable {Aut G2SplitReal : Type*} [Group Aut] [Group G2SplitReal]

/--
Certificate readback for the real split-octonion automorphism classification.

`G2SplitReal` is an explicit carrier for the real split group of type `G₂`
(`G_{2(2)}` in real-form notation), not the finite Chevalley group `G₂(2)`.
The equivalence is read from a supplied classification certificate.
-/
def real_split_octonion_aut_equiv_splitRealG2_from_certificate
    (cp : ZornCompositionDatum ℝ)
    (C : ClassificationCertificate
      (R := ℝ) (Aut := Aut) (G2 := G2SplitReal) cp) :
    Aut ≃* G2SplitReal :=
  C.autEquivG2

/--
Full canonical-product readback packet from a supplied real split classification
certificate.  This is conditional on `cp.mulZ` being the repository canonical
Zorn product and on the explicit certificate `C`.
-/
def real_split_octonion_classification_packet_from_certificate
    (cp : ZornCompositionDatum ℝ)
    (hcp : cp.mulZ = zMul (R := ℝ))
    (C : ClassificationCertificate
      (R := ℝ) (Aut := Aut) (G2 := G2SplitReal) cp) :
    C.ClassificationReadbackPacket :=
  C.classification_certificate_packet hcp

end InfoGeometry.Algebra.Zorn.RealSplitOctonionG2Classification

end noncomputable section
