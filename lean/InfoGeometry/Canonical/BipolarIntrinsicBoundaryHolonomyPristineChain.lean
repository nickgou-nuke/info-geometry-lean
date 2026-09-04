import InfoGeometry.Analysis.BipolarMetricEndLengths
import InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
import InfoGeometry.Canonical.BipolarAngularOneFormConnection
import InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
import Mathlib.Tactic

/-!
# Intrinsic boundary, metric-end, and U(1) holonomy chain

This capstone packages the intrinsic mathematical content recovered from the
image-boundary, metric-completeness, and magnetic-holonomy parts of the informal
stream.

The theorem hierarchy is deliberately strict.

* The vertical bisector is an exact zero set of the logarithmic image
  potential, while its normal derivative is the positive Cauchy kernel.
* After the explicit scalar normalization, the induced boundary density has
  total strength `-Q`.
* The two finite punctures have divergent radial logarithmic length along the
  middle real axis, while the positive-real end at infinity has finite limiting
  length `log 2` from the base point `2`.
* The angular component `dTheta = Im(dlog q · ds)` is a genuine real-linear
  one-form.  Its local scalar curvature vanishes, but its elementary contour
  periods are `+2 pi` and `-2 pi`.
* Exponentiation gives a native Mathlib circle character.  Integral coupling is
  trivial on the integral period lattice; half coupling gives a nontrivial
  order-two elementary phase.

No conductor constitutive law, Maxwell equation, compactly-supported
cohomology representative, arbitrary-loop classification, smooth principal
bundle, distributional flux, BdG Hamiltonian, Andreev amplitude, or
ultrarelativistic shockwave is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain

open Filter MeasureTheory
open scoped Interval Real Topology

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarMetricEndLengths
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
open InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarAngularOneFormConnection

/-- Exact normalized image-boundary packet. -/
theorem pristine_boundary_image_core
    (sourceStrength epsilon y : ℝ) (hepsilon : epsilon ≠ 0) :
    scaledImagePotential sourceStrength epsilon (1 / 2) y = 0 ∧
      deriv (fun x => scaledImagePotential sourceStrength epsilon x y)
          (1 / 2) =
        -(sourceStrength / (2 * Real.pi * epsilon)) * boundaryKernel y ∧
      inducedSurfaceDensity sourceStrength y =
        -epsilon * leftNormalDerivativeAtHalf
          (fun x => scaledImagePotential sourceStrength epsilon x y) ∧
      Integrable (inducedSurfaceDensity sourceStrength) ∧
      (∫ t : ℝ, boundaryKernel t) = 2 * Real.pi ∧
      (∫ t : ℝ, inducedSurfaceDensity sourceStrength t) = -sourceStrength := by
  exact ⟨scaledImagePotential_half sourceStrength epsilon y,
    deriv_scaledImagePotential_half sourceStrength epsilon y,
    inducedSurfaceDensity_eq_neg_epsilon_mul_leftNormalDerivative
      sourceStrength epsilon y hepsilon,
    integrable_inducedSurfaceDensity sourceStrength,
    integral_boundaryKernel,
    integral_inducedSurfaceDensity sourceStrength⟩

/-- Finite-window version of the boundary-density law. -/
theorem pristine_boundary_window_core
    (sourceStrength a b : ℝ) :
    (∫ y in a..b, boundaryKernel y) =
        2 * (Real.arctan (2 * b) - Real.arctan (2 * a)) ∧
      (∫ y in a..b, inducedSurfaceDensity sourceStrength y) =
        -(sourceStrength / Real.pi) *
          (Real.arctan (2 * b) - Real.arctan (2 * a)) := by
  exact ⟨intervalIntegral_boundaryKernel a b,
    intervalIntegral_inducedSurfaceDensity sourceStrength a b⟩

/-- Exact correction to the informal completeness claim.  The theorem records
path lengths only and does not promote them to a global Hopf--Rinow theorem. -/
theorem pristine_metric_end_core :
    Tendsto originTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto oneTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto infinityTruncatedLength atTop (𝓝 (Real.log 2)) := by
  exact bipolar_metric_end_length_packet

/-- The vertical bisector is exactly the zero locus of the radial logarithmic
coordinate on the punctured domain. -/
theorem pristine_bisector_zero_locus
    {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ s.re = 1 / 2 := by
  exact eta_zero_iff_re_eq_half hs

/-- Genuine real angular one-form, local flatness, direct contour periods, and
circle-valued holonomy. -/
theorem pristine_angular_connection_core
    (α : ℝ) {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularOneFormAt s v =
        (InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan.omegaCoeff s * v).im ∧
      angularExteriorDerivativeAt s u v = 0 ∧
      coupledAngularCurvatureAt α s u v = 0 ∧
      angularCircleIntegral 0 r = angularPeriod originWinding ∧
      angularCircleIntegral 1 r = angularPeriod oneWinding ∧
      directContourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      directContourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  exact bipolar_angular_one_form_connection_packet α hs u v hr0 hr1

/-- Integral and half-integral coupling are distinguished exactly. -/
theorem pristine_integral_half_holonomy_core
    (w : WindingPair) :
    u1Holonomy 1 w = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 := by
  exact ⟨u1Holonomy_unit_coupling w,
    u1Holonomy_half_origin_ne_one,
    u1Holonomy_half_origin_sq⟩

/-- Master intrinsic chain.  Every displayed statement is owned by a genuine
analytic or algebraic theorem; the physical realizations remain downstream. -/
theorem pristine_intrinsic_boundary_holonomy_master
    (sourceStrength epsilon α : ℝ) (hepsilon : epsilon ≠ 0)
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (eta s = 0 ↔ s.re = 1 / 2) ∧
      (∫ y : ℝ, inducedSurfaceDensity sourceStrength y) = -sourceStrength ∧
      Tendsto originTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto oneTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto infinityTruncatedLength atTop (𝓝 (Real.log 2)) ∧
      angularExteriorDerivativeAt s u v = 0 ∧
      coupledAngularCurvatureAt α s u v = 0 ∧
      angularCircleIntegral 0 r = 2 * Real.pi ∧
      angularCircleIntegral 1 r = -(2 * Real.pi) ∧
      directContourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      u1Holonomy 1 originWinding = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 := by
  exact ⟨eta_zero_iff_re_eq_half hs,
    integral_inducedSurfaceDensity sourceStrength,
    tendsto_originTruncatedLength,
    tendsto_oneTruncatedLength,
    tendsto_infinityTruncatedLength,
    angularExteriorDerivativeAt_eq_zero s u v,
    coupledAngularCurvatureAt_eq_zero α s u v,
    by simpa using angularCircleIntegral_origin hr0 hr1,
    by simpa using angularCircleIntegral_one hr0 hr1,
    directContourU1Holonomy_origin_eq_winding α hr0 hr1,
    u1Holonomy_unit_coupling originWinding,
    u1Holonomy_half_origin_ne_one⟩

end InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
