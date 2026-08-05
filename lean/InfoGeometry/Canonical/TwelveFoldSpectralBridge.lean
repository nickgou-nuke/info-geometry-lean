import InfoGeometry.Canonical.TwelveFoldSheetColorOmega
import InfoGeometry.Canonical.SixStateSpectralBridge

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldSpectralBridge

open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Canonical.SixStateSpectralBridge
open InfoGeometry.Canonical.TwelveFoldSheetColorOmega

theorem masterTwelve_sq_mulVec_spectralVector
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    masterTwelve ^ 2 *ᵥ spectralVector zeta n =
      (if (sheetColorEquiv n).1 = .positive then
          zeta (sheetColorEquiv n).2
       else -zeta (sheetColorEquiv n).2) • spectralVector zeta n := by
  rw [masterTwelve_sq]
  exact spectralVector_triality zeta hzeta n

end InfoGeometry.Canonical.TwelveFoldSpectralBridge
