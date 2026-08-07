#exit
import InfoGeometry.Canonical.TwelveFoldSheetColorOmega
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldParityCompatibility

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

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
    omegaHat ^ 2 = sixParity := by
  calc
    omegaHat ^ 2 =
        Matrix.kronecker (omegaChi ^ 2) (1 : Mat3C) := by
      simpa [omegaHat] using kronecker_pow_two omegaChi (1 : Mat3C)
    _ = sixParity := by
      have hω : omegaChi ^ 2 = sheetParity := by
        simpa [pow_two] using omegaChi_sq
      rw [hω]
      rfl

theorem sixTriality_cube_eq_omegaHat_sq :
    sixTriality ^ 3 = omegaHat ^ 2 := by
  rw [sixTriality_cube_eq_sixParity, omegaHat_sq_eq_sixParity]

theorem masterTwelve_six_eq_common_parity :
    masterTwelve ^ 6 = sixTriality ^ 3 := by
  rw [masterTwelve_six, sixTriality_cube_eq_sixParity]

end InfoGeometry.Canonical.TwelveFoldParityCompatibility
