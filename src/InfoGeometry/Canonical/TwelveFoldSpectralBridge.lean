import InfoGeometry.Canonical.TwelveFoldExplicitOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SixStateSpectralBridge

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldSpectralBridge

open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Canonical.SixStateSpectralBridge
open InfoGeometry.Canonical.TwelveFoldExplicitOperators

theorem masterTwelve_sq_mulVec_spectralVector
    (zeta : HexColor → ℂ) (hzeta : ∀ a, zeta a ^ 3 = 1)
    (n : HexIndex) :
    TwelveFoldExplicitOperators.masterTwelve ^ 2 *ᵥ spectralVector zeta n =
      (if (sheetColorEquiv n).1 = .positive then
          zeta (sheetColorEquiv n).2
       else -zeta (sheetColorEquiv n).2) • spectralVector zeta n := by
  exact TwelveFoldExplicitOperators.masterTwelve_sq_mulVec_spectralVector
    zeta hzeta n

end InfoGeometry.Canonical.TwelveFoldSpectralBridge
