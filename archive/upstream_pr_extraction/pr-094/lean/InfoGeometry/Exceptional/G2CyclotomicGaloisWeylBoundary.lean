import InfoGeometry.Canonical.TwelveFoldCyclotomicNative
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# Cyclotomic Galois versus `G₂` Weyl cardinality

The cyclotomic and Weyl layers share finite symmetry data, but they are not the
same group: the former is the multiplicative unit group modulo twelve, while
the latter is the twelve-element Coxeter/Weyl carrier.
-/

namespace InfoGeometry.Exceptional.G2CyclotomicGaloisWeylBoundary

open InfoGeometry.Canonical.TwelveFoldCyclotomicNative
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

theorem cyclotomic_galois_card_eq_four :
    Nat.card (Gal(CyclotomicField 12 ℚ / ℚ)) = 4 := by
  exact cyclotomic12_gal_card

theorem g2_weyl_card_eq_twelve :
    Fintype.card WeylG2 = 12 := by
  exact weylG2_card

theorem cyclotomic_galois_card_ne_g2_weyl_card :
    Nat.card (Gal(CyclotomicField 12 ℚ / ℚ)) ≠ Fintype.card WeylG2 := by
  rw [cyclotomic_galois_card_eq_four, g2_weyl_card_eq_twelve]
  norm_num

end InfoGeometry.Exceptional.G2CyclotomicGaloisWeylBoundary
