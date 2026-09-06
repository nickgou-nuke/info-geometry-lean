import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import InfoGeometry.Analysis.BipolarMetricEndLengths
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import InfoGeometry.Analysis.BipolarBoundaryTrace
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.BipolarCartanLorentzBridge

/-!
# Pristine mathematical chain behind the bipolar conformal construction

This file is an architectural capstone with no physical vocabulary in its
statements. It records the exact chain that survives after separating the
conformal, logarithmic, local differential, planar Hodge, winding, and finite
representation layers.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPristineMathematicalChain

open Filter
open scoped Topology

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarMetricEndLengths
open InfoGeometry.Analysis.BipolarLocalConformalCoordinate
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering

/-- Local analytic core. On a compatible branch, `W` is a noncritical local
primitive of the global logarithmic differential. -/
theorem pristine_local_analytic_core
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      HasDerivAt bipolarLog (dlog01 s) s ∧
      dlog01 s = 1 / (s * (1 - s)) ∧
      dlog01 s ≠ 0 ∧
      0 < metricDensity s := by
  exact ⟨exp_bipolarLog hs,
    hasDerivAt_bipolarLog hs hslit,
    dlog01_eq_one_div_mul hs,
    dlog01_ne_zero hs,
    metricDensity_pos hs⟩

/-- Global reflection and Apollonius core. -/
theorem pristine_reflection_apollonius_core
    {s : ℂ} (hs : s ∈ punctured01) (c : ℝ) :
    mirror (mirror s) = s ∧
      (mirror s = s ↔ s.re = 1 / 2) ∧
      crossRatio01 (mirror s) = (Complex.conj (crossRatio01 s))⁻¹ ∧
      eta (mirror s) = -eta s ∧
      (eta s = c ↔ ‖s‖ = Real.exp c * ‖1 - s‖) := by
  exact ⟨mirror_involutive s,
    mirror_fixed_iff s,
    crossRatio01_mirror s,
    eta_mirror s,
    eta_eq_iff_apollonius hs c⟩

/-- Exact zero-level characterization by the critical bisector. -/
theorem pristine_eta_zero_critical_core
    {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ s.re = 1 / 2 :=
  eta_zero_iff_re_eq_half hs

/-- Exact real-coordinate boundary trace and planar Hodge core. -/
theorem pristine_boundary_hodge_core (y : ℝ) :
    phiXY (1 / 2) y = 0 ∧
      deriv (fun t => phiXY t y) (1 / 2) = 1 / ((1 / 4 : ℝ) + y ^ 2) ∧
      dPhiCoeff (1 / 2) y 1 = 0 ∧
      dPsiCoeff (1 / 2) y 0 = 0 ∧
      dPsiCoeff (1 / 2) y 1 = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact ⟨phiXY_half y,
    deriv_phiXY_half y,
    dPhiCoeff_half_tangent_zero y,
    dPsiCoeff_half_normal_zero y,
    dPsiCoeff_half_tangent y⟩

/-- Pointwise Euclidean Hodge relation between the radial and angular forms. -/
theorem pristine_planar_hodge_core (x y : ℝ) :
    dPsiCoeff x y = hodgeRotate (dPhiCoeff x y) ∧
      hodgeRotate (dPsiCoeff x y) = -dPhiCoeff x y := by
  exact planar_hodge_packet x y

/-- The metric coefficient has two finite logarithmic poles but a removable
point at infinity in the inversion chart. -/
theorem pristine_metric_infinity_core
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    inversionPullbackDlog u = 1 / (1 - u) ∧
      infinityChartDensity 0 = 1 := by
  exact ⟨inversionPullbackDlog_eq hu0 hu1, infinityChartDensity_zero⟩

/-- Actual radial length asymptotics of the logarithmic metric: both finite
punctures are infinitely far along the middle real axis, whereas the positive
real escape from `2` to infinity has finite length `log 2`. -/
theorem pristine_metric_end_length_core :
    Tendsto originTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto oneTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto infinityTruncatedLength atTop (𝓝 (Real.log 2)) :=
  bipolar_metric_end_length_packet

/-- The explicit two-generator winding carrier and the period detected by the
residue-difference logarithmic form. -/
theorem pristine_winding_core (w : WindingPair) :
    residuePairing w = (residueWinding w : ℂ) ∧
      circulationPeriod w =
        residuePairing w * (2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod (diagonalWinding w.1) = 0 := by
  exact ⟨residuePairing_eq_difference w,
    circulationPeriod_eq_residuePairing w,
    circulationPeriod_diagonal w.1⟩

/-- Finite determinant-one representation core. -/
theorem pristine_cartan_representation_core
    (s : ℂ) (X : HermitianMat2) :
    halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧
      (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact ⟨halfLogLift_eq_compactK_mul_boostA s,
    halfLogLift_isSL2C s,
    bipolarSolderingAction_det s X⟩

/-- Critical-line specialization in branch-independent form. -/
theorem pristine_critical_line_core (y : ℝ) :
    eta (criticalLine y) = 0 ∧
      crossRatio01 (criticalLine y) = criticalPhase y ∧
      ‖criticalPhase y‖ = 1 ∧
      halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) ∧
      isSU2 (halfLogLift (criticalLine y)) := by
  exact ⟨eta_criticalLine y,
    crossRatio01_criticalLine_eq_criticalPhase y,
    norm_criticalPhase y,
    halfLogLift_criticalLine_eq_compactK y,
    halfLogLift_criticalLine_isSU2 y⟩

/-- Real logistic slice: the open interval is exactly the exponential coordinate
line for the radial logarithmic parameter. -/
theorem pristine_logistic_core (t : ℝ) :
    0 < logistic t ∧
      logistic t < 1 ∧
      crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
      eta (logistic t : ℂ) = t := by
  exact ⟨logistic_pos t,
    logistic_lt_one t,
    crossRatio01_logistic t,
    eta_logistic t⟩

/-- Compact master theorem exposing one theorem from every mathematically
independent global/local layer, without adding physical interpretation. -/
theorem pristine_master_chain
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (X : HermitianMat2) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      HasDerivAt bipolarLog (dlog01 s) s ∧
      dlog01 s = 1 / (s * (1 - s)) ∧
      eta (mirror s) = -eta s ∧
      (mirror s = s ↔ s.re = 1 / 2) ∧
      halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧
      (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact ⟨exp_bipolarLog hs,
    hasDerivAt_bipolarLog hs hslit,
    dlog01_eq_one_div_mul hs,
    eta_mirror s,
    mirror_fixed_iff s,
    halfLogLift_eq_compactK_mul_boostA s,
    halfLogLift_isSL2C s,
    bipolarSolderingAction_det s X⟩

end InfoGeometry.Canonical.BipolarPristineMathematicalChain
