import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.OperatorAlgebra.SplitOctonionG2TypeGenerators
import InfoGeometry.Algebra.Zorn.SplitOctonionG2TwoClassificationBoundary

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
* if an explicit enumeration property gives `|Aut(O_s(F₂))| = 12096`, Lean
  reads it back as equality with the finite `G₂(2)` order.

Open debt:
* no real Lie-group classification identifying `Aut(𝕆_s(ℝ))` with a finite
  `F₂` Chevalley group is proved here;
* no native Lean enumeration of all 12096 finite automorphisms is performed here;
* the finite enumeration remains an executable property lane, read back by a
  conditional Lean theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoSplitZorn

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.CyclicAutomorphism
open InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators

/-- Conditional finite classification readback from an explicit automorphism enumeration. -/
theorem finite_aut_card_eq_g2two_from_enumeration
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    Fintype.card SplitOctF2Aut = g2twoOrder :=
  aut_splitOctF2_card_eq_g2twoOrder_from_enumeration h_enum

end InfoGeometry.Algebra.Zorn.G2TwoSplitZorn
