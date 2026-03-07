import InfoGeometry.ExponentialFamily.GaussianHolonomy

/-!
# InfoGeometry.Canonical.GaussianHolonomy

Canonical facade for Gaussian holonomy and Dirac-field interfaces.
-/

namespace InfoGeometry.Canonical.GaussianHolonomy

export InfoGeometry.ExponentialFamily.GaussianHolonomy (
  gaussianDiracField
  gaussianWilsonLoopDiscrete
  gaussian_holonomy_flat
)

open InfoGeometry.ExponentialFamily.Gaussian
open InfoGeometry.ExponentialFamily.GaussianHolonomy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] theorem gaussianDiracField_apply (G : GaussianFamily E) (x : E) :
    gaussianDiracField G x = G.sigma := rfl

theorem gaussianDiracField_const (G : GaussianFamily E) (x y : E) :
    gaussianDiracField G x = gaussianDiracField G y := by
  simp [gaussianDiracField_apply]

end InfoGeometry.Canonical.GaussianHolonomy
