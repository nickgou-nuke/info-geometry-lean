import Mathlib.GroupTheory.Exponent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import InfoGeometry.Canonical.TwelveFoldArithmeticNative

/-!
# Native cyclotomic shadow of the twelvefold operator

This owner records only the standard arithmetic consequences of order twelve.
It does not identify the concrete matrix representation with a cyclotomic
field, nor does it promote a projective symmetry to a Galois action.
-/

namespace InfoGeometry.Canonical.TwelveFoldCyclotomicNative

open InfoGeometry.Canonical.TwelveFoldArithmeticNative

noncomputable section

theorem primitive_twelfth_root_iff {ζ : ℂ} :
    (Polynomial.cyclotomic 12 ℂ).IsRoot ζ ↔ IsPrimitiveRoot ζ 12 := by
  simpa using (Polynomial.isRoot_cyclotomic_iff (R := ℂ) (n := 12) (μ := ζ))

theorem primitive_twelfth_root_is_cyclotomic_root {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 12) :
    (Polynomial.cyclotomic 12 ℂ).IsRoot ζ :=
  IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 12) (by norm_num) hζ

theorem complex_conj_primitive_twelfth_root_inversion {ζ : ℂˣ}
    (hζ : IsPrimitiveRoot ζ 12) :
    (starRingEnd ℂ) (ζ : ℂ) = (↑ζ⁻¹ : ℂ) := by
  exact Complex.conj_rootsOfUnity hζ.mem_rootsOfUnity

noncomputable def cyclotomic12_galEquivUnits :
    Gal(CyclotomicField 12 ℚ / ℚ) ≃* (ZMod 12)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 12 (CyclotomicField 12 ℚ)

theorem cyclotomic12_gal_card :
    Nat.card (Gal(CyclotomicField 12 ℚ / ℚ)) = 4 := by
  simpa [Nat.card_eq_fintype_card] using
    (Fintype.card_congr cyclotomic12_galEquivUnits.toEquiv).trans
      zmod12_units_card

theorem cyclotomic12_gal_exponent :
    Monoid.exponent (Gal(CyclotomicField 12 ℚ / ℚ)) = 2 := by
  rw [Monoid.exponent_eq_of_mulEquiv cyclotomic12_galEquivUnits]
  exact zmod12_units_exponent_two

theorem cyclotomic12_gal_isKleinFour :
    IsKleinFour (Gal(CyclotomicField 12 ℚ / ℚ)) := by
  exact IsKleinFour.mk cyclotomic12_gal_card cyclotomic12_gal_exponent

theorem cyclotomic12_gal_inversion (σ : Gal(CyclotomicField 12 ℚ / ℚ)) :
    σ⁻¹ = σ := by
  exact inv_eq_self_of_exponent_two cyclotomic12_gal_exponent σ

end
end InfoGeometry.Canonical.TwelveFoldCyclotomicNative
