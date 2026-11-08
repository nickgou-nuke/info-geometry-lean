import Mathlib.Analysis.RCLike.Sqrt
import InfoGeometry.Analysis.ModifiedBesselOrderZero

set_option autoImplicit false

namespace Omega.GU

/-- The quadratic form appearing in the Joukowsky bivariate Bessel kernel. -/
noncomputable def joukowskyBivariateBesselArg (r u v : Complex) : Complex :=
  2 * Complex.sqrt (u ^ 2 + v ^ 2 + (r ^ 2 + (r⁻¹) ^ 2) * u * v)

/-- The Joukowsky bivariate moment-generating expression evaluated through the genuine
order-zero modified Bessel function. -/
noncomputable def joukowskyBivariateMGF (r u v : Complex) : Complex :=
  InfoGeometry.Analysis.ModifiedBessel.I0 (joukowskyBivariateBesselArg r u v)

/-- The bivariate Bessel expression is normalized at the zero source. -/
@[simp] theorem joukowskyBivariateMGF_zero (r : Complex) :
    joukowskyBivariateMGF r 0 0 = 1 := by
  simp [joukowskyBivariateMGF, joukowskyBivariateBesselArg]

end Omega.GU
