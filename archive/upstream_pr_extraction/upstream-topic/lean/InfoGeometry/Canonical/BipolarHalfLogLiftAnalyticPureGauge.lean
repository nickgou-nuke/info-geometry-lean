import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import Mathlib

/-!
# Analytic differential of the bipolar half-log lift

The algebraic identity `G^{-1} dG = A` becomes a genuine local analytic
statement only after the displayed `dG` is connected to the derivative of the
actual branch-dependent half-log lift.  This file supplies that missing local
bridge entry by entry.

The hypotheses place `q(s)` in the principal logarithm slit plane.  No global
single-valued lift is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Analytic derivative matrix of the half-log lift in the unit complex
coordinate direction. -/
def halfLogLiftAnalyticDerivative (s : ℂ) : Matrix2C :=
  (dlog01 s / 2) •
    !![plusWeight s, 0;
       0, -minusWeight s]

/-- Directional analytic differential obtained from complex linearity. -/
def halfLogLiftAnalyticDifferential (s v : ℂ) : Matrix2C :=
  v • halfLogLiftAnalyticDerivative s

/-- On the punctured domain the global-coefficient differential and the
analytic differential coincide. -/
theorem halfLogLiftDifferential_eq_analytic
    {s : ℂ} (hs : s ∈ punctured01) (v : ℂ) :
    halfLogLiftDifferential s v =
      halfLogLiftAnalyticDifferential s v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLiftDifferential, halfLogLiftAnalyticDifferential,
      halfLogLiftAnalyticDerivative, omegaCoeff_eq_dlog01 hs,
      Matrix.smul_apply] <;>
    ring

/-- Every matrix entry of the actual half-log lift has the derivative displayed
by `halfLogLiftAnalyticDerivative`. -/
theorem hasDerivAt_halfLogLift_entry
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (i j : Fin 2) :
    HasDerivAt (fun z : ℂ => halfLogLift z i j)
      (halfLogLiftAnalyticDerivative s i j) s := by
  fin_cases i <;> fin_cases j
  · simpa [halfLogLift, halfLogLiftAnalyticDerivative,
      Matrix.smul_apply] using hasDerivAt_plusWeight hs hslit
  · simpa [halfLogLift, halfLogLiftAnalyticDerivative,
      Matrix.smul_apply] using
      (hasDerivAt_const (x := s) (c := (0 : ℂ)))
  · simpa [halfLogLift, halfLogLiftAnalyticDerivative,
      Matrix.smul_apply] using
      (hasDerivAt_const (x := s) (c := (0 : ℂ)))
  · have hm := hasDerivAt_minusWeight hs hslit
    convert hm using 1 <;>
      simp [halfLogLift, halfLogLiftAnalyticDerivative,
        Matrix.smul_apply] <;>
      ring

/-- Entrywise derivative along the affine complex direction `v`. -/
theorem hasDerivAt_halfLogLift_entry_along
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (v : ℂ) (i j : Fin 2) :
    HasDerivAt (fun t : ℂ => halfLogLift (s + t * v) i j)
      (halfLogLiftAnalyticDifferential s v i j) 0 := by
  have hline : HasDerivAt (fun t : ℂ => s + t * v) v 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℂ)) (c := s)).add
        ((hasDerivAt_id (x := (0 : ℂ))).mul_const v)
  have hcomp := (hasDerivAt_halfLogLift_entry hs hslit i j).comp 0 hline
  convert hcomp using 1 <;>
    simp [halfLogLiftAnalyticDifferential,
      halfLogLiftAnalyticDerivative, Matrix.smul_apply] <;>
    ring

/-- Genuine local pure-gauge factorization for the analytic differential. -/
theorem halfLogLift_local_pure_gauge
    {s : ℂ} (hs : s ∈ punctured01) (v : ℂ) :
    halfLogLiftInv s * halfLogLiftAnalyticDifferential s v =
      variableCartanConnection s v := by
  rw [← halfLogLiftDifferential_eq_analytic hs]
  exact halfLogLiftInv_mul_differential s v

/-- Compact local analytic pure-gauge packet. -/
theorem bipolar_half_log_pure_gauge_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (v : ℂ) (i j : Fin 2) :
    HasDerivAt (fun t : ℂ => halfLogLift (s + t * v) i j)
        (halfLogLiftAnalyticDifferential s v i j) 0 ∧
      halfLogLiftInv s * halfLogLiftAnalyticDifferential s v =
        variableCartanConnection s v := by
  exact ⟨hasDerivAt_halfLogLift_entry_along hs hslit v i j,
    halfLogLift_local_pure_gauge hs v⟩

end InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge
