import InfoGeometry.Analysis.BipolarBoundaryTrace
import InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
import InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
import InfoGeometry.Analysis.BipolarMetricEndLengths
import InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
import InfoGeometry.Canonical.BipolarAngularOneFormConnection

/-! A conservative capstone: boundary trace, metric speed, angular flatness,
and the two elementary holonomy readouts.  It deliberately contains no
physical boundary law or global completeness assertion. -/
noncomputable section
namespace InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
open Set
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
open InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
open InfoGeometry.Analysis.BipolarMetricEndLengths
open InfoGeometry.Canonical.BipolarAngularOneFormConnection
open InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice

theorem pristine_boundary_image_core (sourceStrength epsilon y : ℝ)
    (hepsilon : epsilon ≠ 0) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 ∧
      deriv (fun x => scaledImagePotential sourceStrength epsilon x y) (1 / 2) =
        -(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y ∧
      (∫ t : ℝ, inducedSurfaceDensity sourceStrength t) = -sourceStrength := by
  exact ⟨scaledImagePotential_half sourceStrength epsilon y,
    deriv_scaledImagePotential_half sourceStrength epsilon y,
    integral_inducedSurfaceDensity sourceStrength⟩

theorem pristine_bisector_zero_locus {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ s.re = 1 / 2 := by
  exact InfoGeometry.Analysis.BipolarMetricEndLengths.eta_zero_iff_re_eq_half hs

theorem pristine_angular_flatness (s u v : ℂ) :
    angularExteriorDerivativeAt s u v = 0 ∧
      coupledAngularCurvatureAt 1 s u v = 0 := by
  exact ⟨angularExteriorDerivativeAt_eq_zero s u v,
    coupledAngularCurvatureAt_eq_zero 1 s u v⟩

theorem pristine_elementary_holonomy {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (α : ℝ) :
    contourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      contourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  exact pristine_scalar_u1_holonomy_core hr0 hr1 α

theorem pristine_no_global_logarithmic_primitive :
    ¬ ∃ F : ℂ → ℂ, ∀ z ∈ punctured01,
      HasDerivAt F (dlog01 z) z := by
  exact InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.no_global_dlog01_primitive

end InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
