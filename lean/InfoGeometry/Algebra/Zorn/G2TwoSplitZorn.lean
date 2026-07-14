import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.OperatorAlgebra.SplitOctonionG2TypeGenerators
import InfoGeometry.Algebra.Zorn.SplitOctonionG2ClassificationCertificate

/-!
# Canonical finite split-Zorn `G₂(2)` ledger

This owner module promotes the verified sandbox packet for the finite
split-octonion/Zorn `G₂(2)` lane into the canonical `Algebra/Zorn` namespace.

Closed here:
* the finite `F₂` Zorn carrier has 256 elements;
* the exact order ledger has `|G₂(2)| = 12096`, derived subgroup order `6048`,
  and `|PGL₃(3)| = 5616 ≠ 12096`;
* concrete integer split-octonion automorphism witnesses `rho` and `tau` preserve
  multiplication and determinant;
* if an explicit enumeration certificate gives `|Aut(O_s(F₂))| = 12096`, Lean
  reads it back as equality with the finite `G₂(2)` order.

Open debt:
* no real Lie-group classification identifying `Aut(𝕆_s(ℝ))` with a finite
  `F₂` Chevalley group is proved here;
* no native Lean enumeration of all 12096 finite automorphisms is performed here;
* the finite enumeration remains an executable certificate lane, read back by a
  conditional Lean theorem.
-/

namespace G2TwoSplitZorn

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism
open InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators
open InfoGeometry.Algebra.Zorn.SplitOctonionG2ClassificationCertificate

/-- Exact finite-order packet for the split Zorn `G₂(2)` lane. -/
theorem finite_g2two_order_packet :
    g2twoOrder = 12096 ∧
      psu33Order * 2 = g2twoOrder ∧
      pgl33Order ≠ g2twoOrder ∧
      outerC2WitnessDegree = 63 ∧
      2 * outerC2WitnessTranspositions + outerC2WitnessFixedPoints =
        outerC2WitnessDegree := by
  exact ⟨rfl, psu33_order_is_half_g2two,
    pgl33_order_ne_g2two_order, rfl,
    outerC2Witness_cycle_profile_accounting⟩

/-- The finite split Zorn octonion carrier over `F₂` has `2^8 = 256` elements. -/
theorem splitOctF2_card_packet :
    Fintype.card SplitOctF2 = 256 :=
  splitOctF2_card

/-- Concrete integer split-octonion `G₂(2)`-type generator witnesses. -/
theorem integer_generator_witness_packet :
    (∀ X Y : SplitOct, rho (mulZ X Y) = mulZ (rho X) (rho Y)) ∧
      (∀ X : SplitOct, rho (rho (rho X)) = X) ∧
      (∀ X : SplitOct, detZ (rho X) = detZ X) ∧
      (∀ X Y : SplitOct, tau (mulZ X Y) = mulZ (tau X) (tau Y)) ∧
      (∀ X : SplitOct, tau (tau X) = X) ∧
      (∀ X : SplitOct, detZ (tau X) = detZ X) := by
  exact ⟨rho_mulZ, rho_order_three, rho_detZ,
    tau_mulZ, tau_order_two, tau_detZ⟩

/-- Conditional finite classification readback from an explicit automorphism enumeration. -/
theorem finite_aut_card_eq_g2two_from_enumeration
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    Fintype.card SplitOctF2Aut = g2twoOrder :=
  aut_splitOctF2_card_eq_g2twoOrder_from_enumeration h_enum

/-- Computational evidence values recorded in the certificate owner. -/
theorem certificate_evidence_packet :
    computationalEvidenceInvariants.rootCount = 12 ∧
      computationalEvidenceInvariants.weylOrder = 12 ∧
      computationalEvidenceInvariants.derivationDimension = 14 ∧
      computationalEvidenceInvariants.atlasG2TwoOrder = 12096 :=
  computationalEvidenceInvariants_packet

end G2TwoSplitZorn
