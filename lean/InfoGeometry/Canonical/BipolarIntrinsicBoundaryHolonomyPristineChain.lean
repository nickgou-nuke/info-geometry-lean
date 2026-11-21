/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BipolarBoundaryTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
import InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
import InfoGeometry.Analysis.BipolarMetricEndLengths
import InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
import InfoGeometry.Canonical.BipolarContourSpinHolonomy
import InfoGeometry.Canonical.BipolarSpinHolonomy
import InfoGeometry.Canonical.BipolarAngularOneFormConnection

/-! A conservative capstone: boundary trace, metric speed, angular flatness,
and the two elementary holonomy readouts.  It deliberately contains no
physical boundary law or global completeness assertion. -/
noncomputable section
namespace InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
open scoped Topology
open Filter
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
open InfoGeometry.Canonical.BipolarContourSpinHolonomy
open InfoGeometry.Canonical.BipolarSpinHolonomy
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

theorem pristine_boundary_window_core
    (sourceStrength a b : ℝ) :
    (∫ y in a..b, boundaryKernel y) =
        2 * (Real.arctan (2 * b) - Real.arctan (2 * a)) ∧
      (∫ y in a..b, inducedSurfaceDensity sourceStrength y) =
        -(sourceStrength / Real.pi) *
          (Real.arctan (2 * b) - Real.arctan (2 * a)) := by
  exact ⟨intervalIntegral_boundaryKernel a b,
    intervalIntegral_inducedSurfaceDensity sourceStrength a b⟩

theorem pristine_metric_end_core :
    Tendsto originTruncatedLength (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop ∧
      Tendsto oneTruncatedLength (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop ∧
      Tendsto infinityTruncatedLength atTop (nhds (Real.log 2)) := by
  exact bipolar_metric_end_length_packet

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

theorem pristine_regular_circle_holonomy_core
    (α : ℝ) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ Metric.sphere c r)
    (h1 : (1 : ℂ) ∉ Metric.sphere c r)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∮ z in C(c, r), dlog01 z) =
        circulationPeriod (circleEnclosurePair c r) ∧
      Complex.exp (∮ z in C(c, r), dlog01 z) = 1 ∧
      contourU1Holonomy α c r =
        u1Holonomy α (circleEnclosurePair c r) ∧
      contourSpinHolonomy c r =
        spinHolonomy (circleEnclosurePair c r) ∧
      contourSpinHolonomy c r * contourSpinHolonomy c r =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      contourSpinHolonomy c r * X * contourSpinHolonomy c r = X := by
  exact ⟨circleIntegral_dlog01_eq_circulationPeriod hr h0 h1,
    exp_circleIntegral_dlog01 hr h0 h1,
    contourU1Holonomy_eq_winding α hr h0 h1,
    contourSpinHolonomy_eq_winding hr h0 h1,
    contourSpinHolonomy_sq hr h0 h1,
    contourSpinHolonomy_adjoint_trivial hr h0 h1 X⟩

theorem pristine_integral_half_holonomy_core
    (w : WindingPair) :
    u1Holonomy 1 w = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 := by
  exact ⟨u1Holonomy_unit_coupling w,
    u1Holonomy_half_origin_ne_one,
    u1Holonomy_half_origin_sq⟩

theorem pristine_intrinsic_boundary_holonomy_master
    (sourceStrength α : ℝ)
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (eta s = 0 ↔ s.re = 1 / 2) ∧
      (∫ y : ℝ, inducedSurfaceDensity sourceStrength y) = -sourceStrength ∧
      Tendsto originTruncatedLength (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop ∧
      Tendsto oneTruncatedLength (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop ∧
      Tendsto infinityTruncatedLength atTop (nhds (Real.log 2)) ∧
      angularExteriorDerivativeAt s u v = 0 ∧
      coupledAngularCurvatureAt α s u v = 0 ∧
      angularCircleIntegral 0 r = 2 * Real.pi ∧
      angularCircleIntegral 1 r = -(2 * Real.pi) ∧
      directContourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      u1Holonomy 1 originWinding = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      ¬ ∃ F : ℂ → ℂ, ∀ z ∈ punctured01,
        HasDerivAt F (dlog01 z) z := by
  exact ⟨Analysis.BipolarMetricEndLengths.eta_zero_iff_re_eq_half hs,
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
    u1Holonomy_half_origin_ne_one,
    no_global_dlog01_primitive⟩

end InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
