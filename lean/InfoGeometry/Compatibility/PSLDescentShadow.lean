import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
Compatibility names for the native projective descent theorems.
-/

open UpperHalfPlane

namespace InfoGeometry.Compatibility

/-- Compatibility export of real central-sign invariance. -/
theorem sl2r_kernel_trivial_on_base
    (g : InfoGeometry.Canonical.PSLDescent.SL2R)
    (tau : UpperHalfPlane) :
    (-g) • tau = g • tau :=
  InfoGeometry.Canonical.PSLDescent.sl2r_neg_smul g tau

/-- Compatibility export of integral central-sign invariance. -/
theorem sl2z_kernel_trivial_on_base
    (g : InfoGeometry.Canonical.PSLDescent.SL2Z)
    (tau : UpperHalfPlane) :
    (-g) • tau = g • tau :=
  InfoGeometry.Canonical.PSLDescent.sl2z_neg_smul g tau

end InfoGeometry.Compatibility
