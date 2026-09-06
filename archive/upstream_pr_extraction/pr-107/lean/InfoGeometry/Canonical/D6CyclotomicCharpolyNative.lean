import InfoGeometry.Canonical.SixStateCharacteristicPolynomial

namespace InfoGeometry.Canonical.D6CyclotomicCharpolyNative

open Polynomial
open InfoGeometry.Canonical.SixStateCharacteristicPolynomial
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
The six-state triality operator is the concrete order-six rotation already
owned by `SixStateCharacteristicPolynomial`.  This file only exposes its
factorization with Mathlib's named cyclotomic polynomials.
-/

theorem sixTriality_charpoly_named_cyclotomic :
    sixTriality.charpoly =
      Polynomial.cyclotomic 1 ℂ * Polynomial.cyclotomic 2 ℂ *
        Polynomial.cyclotomic 3 ℂ * Polynomial.cyclotomic 6 ℂ := by
  rw [sixTriality_charpoly]
  simp [Polynomial.cyclotomic_one, Polynomial.cyclotomic_two,
    Polynomial.cyclotomic_three, Polynomial.cyclotomic_six]
  ring

end InfoGeometry.Canonical.D6CyclotomicCharpolyNative
