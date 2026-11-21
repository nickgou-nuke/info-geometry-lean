/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarContourSpinHolonomy
import InfoGeometry.Canonical.BipolarContourPeriodSchwarzianWardPristineChain
import Mathlib.Tactic

/-! Compact capstone for the analytic contour-to-U(1) and spin readouts. -/
noncomputable section
namespace InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
open scoped Interval Real
open Complex Metric
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingExactSequence
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarContourSpinHolonomy
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge

theorem pristine_scalar_u1_holonomy_core {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (α : ℝ) :
    contourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
    contourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  exact ⟨contourU1Holonomy_origin (α := α) hr0 hr1,
    contourU1Holonomy_one (α := α) hr0 hr1⟩

theorem pristine_unit_half_spin_distinction {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    contourSpinHolonomy 0 r =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  contourSpinHolonomy_origin hr0 hr1

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
    (by
      rw [contourU1Holonomy_origin hr0 hr1]
      exact u1Holonomy_unit_coupling originWinding),
    (by
      rw [contourU1Holonomy_origin hr0 hr1]
      exact u1Holonomy_half_origin_ne_one),
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    (by simp [ProjectiveVectorField.third]),
    (by simpa using spinHolonomy_origin),
    originHolonomy_adjoint_trivial X⟩

end InfoGeometry.Canonical.BipolarContourU1HolonomyPristineChain
