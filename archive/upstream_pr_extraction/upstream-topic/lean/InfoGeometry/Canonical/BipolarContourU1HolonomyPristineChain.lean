import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import InfoGeometry.Canonical.BipolarContourPeriodSchwarzianWardPristineChain
import Mathlib.Tactic

/-!
# Contour, scalar U(1) holonomy, Schwarzian, and Ward pristine chain

This capstone adds the scalar circle-valued holonomy layer to the already
certified contour/period/Schwarzian/Ward chain.

The distinction is exact:

* `Complex.exp (∮ dlog01) = 1` is the full logarithmic character;
* `u1Holonomy α` is the circle character of the angular period `α ∮ dθ`;
* integral `α` gives trivial holonomy on the installed integral winding lattice;
* `α = 1/2` gives a nontrivial order-two elementary phase;
* the matrix half-Cartan holonomy is a separate spinorial lift whose central
  sign is invisible under adjoint conjugation.

No smooth gauge bundle, arbitrary-loop classification, distributional flux, or
microscopic Aharonov--Bohm dynamics is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain

open scoped Interval Real
open Complex Metric
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarWindingExactSequence
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge

/-- Exact scalar period and elementary contour-holonomy packet. -/
theorem pristine_scalar_u1_holonomy_core
    (α : ℝ) (w : WindingPair)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circulationPeriod w = (angularPeriod w : ℂ) * Complex.I ∧
      u1Holonomy α (originWinding + oneWinding) = 1 ∧
      contourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      contourU1Holonomy α 1 r = u1Holonomy α oneWinding ∧
      u1Holonomy 1 w = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 := by
  exact bipolar_u1_period_holonomy_packet α w hr0 hr1

/-- Unit scalar holonomy, half-coupled scalar holonomy, and spinorial central
holonomy are distinct finite representations of the same installed period
carrier. -/
theorem pristine_unit_half_spin_distinction
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    contourU1Holonomy 1 0 r = 1 ∧
      contourU1Holonomy (1 / 2 : ℝ) 0 r ≠ 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨(contourU1Holonomy_unit_elementary hr0 hr1).1,
    contourU1Holonomy_half_origin_ne_one hr0 hr1,
    u1Holonomy_half_origin_sq,
    spinHolonomy_origin,
    originHolonomy_adjoint_trivial X⟩

/-- Master readback from genuine elementary contour integration to scalar
circle holonomy, exponential covering, logarithmic Schwarzian, normalized
projective connection, projective anomaly cancellation, and the central
spinorial double-cover sign. -/
theorem pristine_contour_u1_schwarzian_ward_master
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (v : ProjectiveVectorField)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∮ z in C(0, r), dlog01 z) = circulationPeriod originWinding ∧
      contourU1Holonomy 1 0 r = 1 ∧
      contourU1Holonomy (1 / 2 : ℝ) 0 r ≠ 1 ∧
      circulationPeriodHom.range = twoPiIPeriodSubgroup ∧
      crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      bipolarProjectiveConnection c s =
        -(c / 24) * dlog01 s ^ 2 ∧
      (c / 12) * v.third s = 0 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1,
    (contourU1Holonomy_unit_elementary hr0 hr1).1,
    contourU1Holonomy_half_origin_ne_one hr0 hr1,
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    projectiveVectorField_centralTerm_zero c v s,
    spinHolonomy_origin,
    originHolonomy_adjoint_trivial X⟩

end InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
