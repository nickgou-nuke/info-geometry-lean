import InfoGeometry.Canonical.TwelveFoldExplicitOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldParityCompatibility

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

/-!
# Common parity of the sixfold and quartic sheet symmetries

This owner records the explicit compatibility equations between the already
defined sixfold triality, the quartic sheet phase, and the twelvefold lift.
It does not identify the associative matrix algebra with a split-octonion
product.
-/

theorem sixTriality_cube_eq_sixParity :
    sixTriality ^ 3 = sixParity := by
  calc
    sixTriality ^ 3 =
        Matrix.kronecker (sheetParity ^ 3) (colorShift ^ 3) := by
      simpa [sixTriality] using kronecker_pow_three sheetParity colorShift
    _ = sixParity := by
      have hparity : sheetParity ^ 3 = sheetParity := by
        simpa [pow_succ, sheetParity_sq]
      rw [hparity, colorShift_cubed]
      rfl

theorem omegaHat_sq_eq_sixParity :
    TwelveFoldExplicitOperators.omegaHat ^ 2 = sixParity := by
  calc
    TwelveFoldExplicitOperators.omegaHat ^ 2 = sixParity :=
      TwelveFoldExplicitOperators.omegaHat_sq

theorem sixTriality_cube_eq_omegaHat_sq :
    sixTriality ^ 3 = TwelveFoldExplicitOperators.omegaHat ^ 2 := by
  rw [sixTriality_cube_eq_sixParity, omegaHat_sq_eq_sixParity]

theorem masterTwelve_six_eq_common_parity :
    TwelveFoldExplicitOperators.masterTwelve ^ 6 = sixTriality ^ 3 := by
  rw [TwelveFoldExplicitOperators.masterTwelve_six,
    sixTriality_cube_eq_sixParity]

end InfoGeometry.Canonical.TwelveFoldParityCompatibility
