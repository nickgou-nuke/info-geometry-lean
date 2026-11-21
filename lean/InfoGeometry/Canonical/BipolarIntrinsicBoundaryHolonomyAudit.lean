/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarDeckPathClass

/-!
# Transitive axiom inspection for the intrinsic boundary and holonomy chain

This module is an executable audit surface.  It adds no mathematical claims;
the `#print axioms` commands expose the transitive dependencies of the public
theorems so that project-specific axioms and `sorryAx` cannot be hidden behind
the capstone.
-/

#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.boundaryKernel_eq_four_mul_inv_one_add_sq
#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.integrable_boundaryKernel
#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.integral_boundaryKernel
#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.hasDerivAt_scaledImagePotential_half
#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.inducedSurfaceDensity_eq_neg_epsilon_mul_leftNormalDerivative
#print axioms InfoGeometry.Analysis.BipolarBoundarySurfaceCharge.integral_inducedSurfaceDensity
#print axioms InfoGeometry.Analysis.BipolarBoundaryKernelIntegral.intervalIntegral_boundaryKernel
#print axioms InfoGeometry.Analysis.BipolarBoundaryKernelIntegral.intervalIntegral_inducedSurfaceDensity

#print axioms InfoGeometry.Analysis.BipolarMetricEndLengths.tendsto_originTruncatedLength
#print axioms InfoGeometry.Analysis.BipolarMetricEndLengths.tendsto_oneTruncatedLength
#print axioms InfoGeometry.Analysis.BipolarMetricEndLengths.tendsto_infinityTruncatedLength

#print axioms InfoGeometry.Canonical.BipolarU1PeriodHolonomy.circulationPeriod_eq_angularPeriod_mul_I
#print axioms InfoGeometry.Canonical.BipolarU1PeriodHolonomy.u1Holonomy_integer_coupling
#print axioms InfoGeometry.Canonical.BipolarU1PeriodHolonomy.u1Holonomy_half_origin_ne_one
#print axioms InfoGeometry.Canonical.BipolarU1PeriodHolonomy.u1Holonomy_half_origin_sq

#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularOneFormAt_eq_omegaCoeff
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularDirectionalDerivative_analytic_witness
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularExteriorDerivativeAt_eq_zero
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.coupledAngularCurvatureAt_eq_zero
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularCircleIntegral_eq_contourAngularPeriod
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularCircleIntegral_origin
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.angularCircleIntegral_one
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.directContourU1Holonomy_origin_eq_winding
#print axioms InfoGeometry.Canonical.BipolarAngularOneFormConnection.directContourU1Holonomy_one_eq_winding

#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_dlog01_eq_circulationPeriod
#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.no_global_dlog01_primitive
#print axioms InfoGeometry.Canonical.BipolarContourSpinHolonomy.contourSpinHolonomy_eq_winding
#print axioms InfoGeometry.Canonical.BipolarContourSpinHolonomy.contourSpinHolonomy_adjoint_trivial

#print axioms InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain.pristine_boundary_image_core
#print axioms InfoGeometry.Analysis.BipolarMetricEndLengths.eta_zero_iff_re_eq_half
#print axioms InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain.pristine_bisector_zero_locus
#print axioms InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain.pristine_angular_flatness
#print axioms InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain.pristine_elementary_holonomy
#print axioms InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain.pristine_no_global_logarithmic_primitive

#print axioms InfoGeometry.Canonical.BipolarDeckPathClass.deckTransport_involutive
#print axioms InfoGeometry.Canonical.BipolarDeckPathClass.deckTransport_energy
#print axioms InfoGeometry.Canonical.BipolarDeckPathClass.deckPathTwice_homotopic_refl
#print axioms InfoGeometry.Canonical.BipolarDeckPathClass.deckPathClass_invariant

noncomputable section

namespace InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain

open Metric Filter MeasureTheory
open scoped Interval Real _root_.Topology
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarMetricEndLengths
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Analysis.BipolarBoundarySurfaceCharge
open InfoGeometry.Analysis.BipolarBoundaryKernelIntegral
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarAngularOneFormConnection
open InfoGeometry.Canonical.BipolarContourSpinHolonomy

/-- Master intrinsic chain.  Every displayed statement is owned by a genuine
analytic or algebraic theorem; the physical realizations remain downstream. -/
theorem pristine_intrinsic_boundary_holonomy_master
    (sourceStrength α : ℝ)
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
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      ¬ ∃ F : ℂ → ℂ, ∀ z ∈ punctured01,
        HasDerivAt F (dlog01 z) z := by
  exact ⟨InfoGeometry.Analysis.BipolarMetricEndLengths.eta_zero_iff_re_eq_half hs,
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
    InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.no_global_dlog01_primitive⟩

end InfoGeometry.Canonical.BipolarIntrinsicBoundaryHolonomyPristineChain
