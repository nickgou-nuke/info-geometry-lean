import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import InfoGeometry.Canonical.BipolarSchwarzianWardPristineChain
import Mathlib.Tactic

/-!
# Genuine contour-to-Schwarzian-Ward pristine chain

The earlier period owner separates two facts:

* the full winding carrier is the explicit lattice `ℤ × ℤ`;
* the residue-difference form has cyclic image `2πiℤ` and diagonal kernel.

`BipolarElementaryContourPeriods` now supplies the missing local analytic
readback: the actual full logarithmic differential `dlog01` integrates to
`+2πi` and `-2πi` on sufficiently small positive circles around `0` and `1`.
This file welds those contour integrals to the already-proved exponential
covering, adjoint-character descent, Schwarzian projective connection, and
projective Virasoro Ward law.

The full exponential kills each elementary contour period.  The half-Cartan
lift can nevertheless retain the central sign `-I₂`, which acts nontrivially on
spinors but trivially by matrix conjugation.  Thus branch independence of the
adjoint root actions does not erase the double-cover monodromy.

No classification of arbitrary loops, path-ordered holonomy theorem, CFT state,
vacuum expectation value, positivity statement, or physical stress tensor is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarContourPeriodSchwarzianWardPristineChain

open scoped Interval Real
open Complex Metric
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarWindingExactSequence
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Physics.ChiralCausalCone

/-- The actual full bipolar one-form realizes the two elementary algebraic
winding periods on small positively oriented circles. -/
theorem pristine_bipolar_elementary_contours
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C(0, r), dlog01 z) = circulationPeriod originWinding ∧
      (∮ z in C((1 : ℂ), r), dlog01 z) = circulationPeriod oneWinding := by
  exact bipolar_elementary_contour_period_packet hr0 hr1

/-- Both actual elementary contour periods are killed by the full exponential
character. -/
theorem exp_elementary_bipolar_contours
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Complex.exp (∮ z in C(0, r), dlog01 z) = 1 ∧
      Complex.exp (∮ z in C((1 : ℂ), r), dlog01 z) = 1 := by
  constructor
  · rw [circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1]
    exact exp_circulationPeriod originWinding
  · rw [circleIntegral_dlog01_one_eq_circulationPeriod hr0 hr1]
    exact exp_circulationPeriod oneWinding

/-- Full-character triviality and half-Cartan monodromy coexist on the genuine
origin contour.  The central half-period sign disappears under adjoint matrix
conjugation. -/
theorem elementary_contour_full_half_character_distinction
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Complex.exp (∮ z in C(0, r), dlog01 z) = 1 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨(exp_elementary_bipolar_contours hr0 hr1).1,
    spinHolonomy_origin,
    originHolonomy_adjoint_trivial X⟩

/-- Complete local-to-global packet from genuine elementary contours through
period descent to the logarithmic Schwarzian, normalized projective connection,
projective Ward anomaly cancellation, and branch-independent adjoint weights. -/
theorem pristine_contour_period_schwarzian_ward_master
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (v : ProjectiveVectorField)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∮ z in C(0, r), dlog01 z) = circulationPeriod originWinding ∧
      (∮ z in C((1 : ℂ), r), dlog01 z) = circulationPeriod oneWinding ∧
      Complex.exp (∮ z in C(0, r), dlog01 z) = 1 ∧
      circulationPeriodHom.range = twoPiIPeriodSubgroup ∧
      HasDerivAt bipolarLog (logarithmicJet₁ s) s ∧
      crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      bipolarProjectiveConnection c s =
        -(c / 24) * dlog01 s ^ 2 ∧
      deriv (bipolarProjectiveConnection c) s =
        bipolarProjectiveConnectionDeriv c s ∧
      (c / 12) * v.third s = 0 ∧
      descendedExp (bipolarLogClass s) = crossRatio01 s ∧
      finiteAdjointFlow s σPlus =
        descendedExp (bipolarLogClass s) • σPlus ∧
      finiteAdjointFlow s σMinus =
        (descendedExp (bipolarLogClass s))⁻¹ • σMinus ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X ∧
      regularizedAtZero c 0 = doublePoleCoefficient c ∧
      regularizedAtOne c 1 = doublePoleCoefficient c := by
  exact ⟨circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1,
    circleIntegral_dlog01_one_eq_circulationPeriod hr0 hr1,
    (exp_elementary_bipolar_contours hr0 hr1).1,
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    (local_bipolarLog_thirdJet hs hslit).1,
    crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    deriv_bipolarSchwarzian_readout hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    deriv_bipolarProjectiveConnection c hs,
    projectiveVectorField_centralTerm_zero c v s,
    descendedExp_bipolarLogClass hs,
    finiteAdjointFlow_sigmaPlus_descends hs,
    finiteAdjointFlow_sigmaMinus_descends hs,
    originHolonomy_adjoint_trivial X,
    regularizedAtZero_zero c,
    regularizedAtOne_one c⟩

end InfoGeometry.Canonical.BipolarContourPeriodSchwarzianWardPristineChain
