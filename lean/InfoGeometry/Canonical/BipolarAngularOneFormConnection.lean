import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import Mathlib.Tactic

/-! The angular component of the bipolar logarithmic differential, treated as
an honest real-linear one-form.  The target is abelian, so its local curvature
is the alternating derivative alone. -/
noncomputable section
namespace InfoGeometry.Canonical.BipolarAngularOneFormConnection
open Complex Set
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan

def angularOneFormAt (s : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun v := (dlog01 s * v).im
  map_add' u v := by simp [mul_add]
  map_smul' c v := by
    change (dlog01 s * ((c : ℂ) * v)).im = c * (dlog01 s * v).im
    simp [Complex.mul_re, Complex.mul_im]
    ring

@[simp] theorem angularOneFormAt_apply (s v : ℂ) :
    angularOneFormAt s v = (dlog01 s * v).im := rfl

@[simp] theorem angularOneFormAt_one (s : ℂ) :
    angularOneFormAt s 1 = (dlog01 s).im := by simp [angularOneFormAt]

@[simp] theorem angularOneFormAt_I (s : ℂ) :
    angularOneFormAt s Complex.I = (dlog01 s).re := by
  simp [angularOneFormAt, Complex.mul_im]

theorem angularOneFormAt_eq_omegaCoeff {s : ℂ} (hs : s ∈ punctured01) (v : ℂ) :
    angularOneFormAt s v = (omegaCoeff s * v).im := by
  rw [angularOneFormAt_apply, omegaCoeff_eq_dlog01 hs]

def angularDirectionalDerivative (s u v : ℂ) : ℝ :=
  (omegaCoeffDeriv s * u * v).im

/-- The angular coefficient has the stated derivative along real tangent lines. -/
theorem angularDirectionalDerivative_analytic_witness
    {s : ℂ} (hs : s ∈ punctured01) (u v : ℂ) :
    HasDerivAt (fun t : ℝ => angularOneFormAt (s + (t : ℂ) * u) v)
      (angularDirectionalDerivative s u v) 0 := by
  have hreal := ((hasDerivAt_omegaCoeff_along hs u).mul_const v).comp_ofReal
  have h := (Complex.imCLM.hasFDerivAt.comp 0 hreal).hasDerivAt
  have heq (z : ℂ) : dlog01 z = omegaCoeff z := by
    simp only [dlog01, omegaCoeff, one_div]
    rw [show (1 : ℂ) - z = -(z - 1) by ring, inv_neg]
    rfl
  simpa [angularOneFormAt_apply, heq, angularDirectionalDerivative] using h

def angularExteriorDerivativeAt (s u v : ℂ) : ℝ :=
  angularDirectionalDerivative s u v - angularDirectionalDerivative s v u

theorem angularExteriorDerivativeAt_eq_zero (s u v : ℂ) :
    angularExteriorDerivativeAt s u v = 0 := by
  unfold angularExteriorDerivativeAt angularDirectionalDerivative
  have : omegaCoeffDeriv s * u * v = omegaCoeffDeriv s * v * u := by ring
  rw [this, sub_self]

def coupledAngularCurvatureAt (α : ℝ) (s u v : ℂ) : ℝ :=
  α * angularExteriorDerivativeAt s u v

@[simp] theorem coupledAngularCurvatureAt_eq_zero (α : ℝ) (s u v : ℂ) :
    coupledAngularCurvatureAt α s u v = 0 := by
  rw [coupledAngularCurvatureAt, angularExteriorDerivativeAt_eq_zero, mul_zero]

/-- Pullback of the real angular one-form by the native circle parametrization. -/
def angularCirclePullback (c : ℂ) (r t : ℝ) : ℝ :=
  angularOneFormAt (circleMap c r t) (deriv (circleMap c r) t)

/-- Integral of the real one-form over one positively oriented turn. -/
def angularCircleIntegral (c : ℂ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), angularCirclePullback c r t

/-- Real integration of the angular form agrees with the imaginary contour readout. -/
theorem angularCircleIntegral_eq_contourAngularPeriod
    {c : ℂ} {r : ℝ} (h : CircleIntegrable dlog01 c r) :
    angularCircleIntegral c r = BipolarU1PeriodHolonomy.contourAngularPeriod c r := by
  unfold angularCircleIntegral angularCirclePullback angularOneFormAt
    BipolarU1PeriodHolonomy.contourAngularPeriod
  rw [circleIntegral]
  simpa [smul_eq_mul, mul_comm] using
    (Complex.imCLM.intervalIntegral_comp_comm h.out)

/-- The actual real one-form integral evaluates to the enclosure period. -/
theorem angularCircleIntegral_eq_angularPeriod_enclosure
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ Metric.sphere c r)
    (h1 : (1 : ℂ) ∉ Metric.sphere c r) :
    angularCircleIntegral c r = BipolarU1PeriodHolonomy.angularPeriod
      (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleEnclosurePair c r) := by
  rw [angularCircleIntegral_eq_contourAngularPeriod
    (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegrable_dlog01_of_avoids_punctures
      hr h0 h1), BipolarU1PeriodHolonomy.contourAngularPeriod,
    InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_dlog01_eq_circulationPeriod
      hr h0 h1, BipolarU1PeriodHolonomy.circulationPeriod_im_eq_angularPeriod]

/-- The positively oriented elementary origin circle has angular period `2π`. -/
theorem angularCircleIntegral_origin {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularCircleIntegral 0 r = BipolarU1PeriodHolonomy.angularPeriod
      InfoGeometry.Analysis.BipolarWindingPeriodLattice.originWinding := by
  have h0 : (0 : ℂ) ∉ Metric.sphere (0 : ℂ) r := by
    simpa [Metric.mem_sphere] using hr0.ne
  have h1 : (1 : ℂ) ∉ Metric.sphere (0 : ℂ) r := by
    simpa [Metric.mem_sphere] using hr1.ne'
  rw [angularCircleIntegral_eq_contourAngularPeriod
    (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegrable_dlog01_of_avoids_punctures
      hr0.le h0 h1), BipolarU1PeriodHolonomy.contourAngularPeriod_origin hr0 hr1]

/-- The positively oriented elementary sink circle has angular period `-2π`. -/
theorem angularCircleIntegral_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularCircleIntegral 1 r = BipolarU1PeriodHolonomy.angularPeriod
      InfoGeometry.Analysis.BipolarWindingPeriodLattice.oneWinding := by
  have h0 : (0 : ℂ) ∉ Metric.sphere (1 : ℂ) r := by
    simpa [Metric.mem_sphere] using hr1.ne'
  have h1 : (1 : ℂ) ∉ Metric.sphere (1 : ℂ) r := by
    simpa [Metric.mem_sphere] using hr0.ne
  rw [angularCircleIntegral_eq_contourAngularPeriod
    (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegrable_dlog01_of_avoids_punctures
      hr0.le h0 h1), BipolarU1PeriodHolonomy.contourAngularPeriod_one hr0 hr1]

/- The direct character is defined from the real pullback integral itself. -/
def directContourU1Holonomy (α : ℝ) (c : ℂ) (r : ℝ) : Circle :=
  Circle.exp (α * angularCircleIntegral c r)

theorem directContourU1Holonomy_eq_contourU1Holonomy
    (α : ℝ) {c : ℂ} {r : ℝ}
    (h : CircleIntegrable dlog01 c r) :
    directContourU1Holonomy α c r = BipolarU1PeriodHolonomy.contourU1Holonomy α c r := by
  rw [directContourU1Holonomy, BipolarU1PeriodHolonomy.contourU1Holonomy,
    angularCircleIntegral_eq_contourAngularPeriod h]

theorem directContourU1Holonomy_origin_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    directContourU1Holonomy α 0 r =
      BipolarU1PeriodHolonomy.u1Holonomy α
        InfoGeometry.Analysis.BipolarWindingPeriodLattice.originWinding := by
  rw [directContourU1Holonomy_eq_contourU1Holonomy α
      (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegrable_dlog01_of_avoids_punctures
        hr0.le (by simpa [Metric.mem_sphere] using hr0.ne)
          (by simpa [Metric.mem_sphere] using hr1.ne')),
    BipolarU1PeriodHolonomy.contourU1Holonomy_origin hr0 hr1]

theorem directContourU1Holonomy_one_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    directContourU1Holonomy α 1 r =
      BipolarU1PeriodHolonomy.u1Holonomy α
        InfoGeometry.Analysis.BipolarWindingPeriodLattice.oneWinding := by
  rw [directContourU1Holonomy_eq_contourU1Holonomy α
      (InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegrable_dlog01_of_avoids_punctures
        hr0.le (by simpa [Metric.mem_sphere] using hr1.ne')
          (by simpa [Metric.mem_sphere] using hr0.ne)),
    BipolarU1PeriodHolonomy.contourU1Holonomy_one hr0 hr1]

end InfoGeometry.Canonical.BipolarAngularOneFormConnection
