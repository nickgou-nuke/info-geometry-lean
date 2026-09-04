import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import Mathlib.Tactic

/-!
# Real angular one-form and direct scalar contour holonomy

The complex logarithmic differential decomposes on the real tangent plane as

`dlog q = d eta + i d theta`.

This file extracts the angular component as a genuine real-linear one-form

`dTheta_s(v) = Im (dlog01(s) * v)`.

It then defines its ordinary real interval integral along Mathlib's native
circle parameterization and proves that this direct real integral is the
imaginary part of the already certified complex contour integral.  Hence the
small elementary circles have angular periods `+2 pi` and `-2 pi`.

The local exterior derivative is represented by alternating the actual
holomorphic derivative coefficient.  It vanishes because the coefficient is
symmetric in the two tangent directions.  Since the scalar target is abelian,
this is the complete local curvature calculation for the modeled `U(1)`
connection `alpha dTheta`.

No arbitrary-loop classification, smooth principal bundle, distributional
extension through the punctures, magnetic field equation, or Aharonov--Bohm
experiment is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarAngularOneFormConnection

open scoped Interval Real
open Complex Metric Set
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan

/-- Angular component of the logarithmic differential as a real-linear
one-form on the complex tangent plane. -/
def angularOneFormAt (s : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun v := (dlog01 s * v).im
  map_add' u v := by
    simp [mul_add]
  map_smul' c v := by
    change (dlog01 s * ((c : ℂ) * v)).im =
      c * (dlog01 s * v).im
    simp [Complex.mul_re, Complex.mul_im]
    ring

@[simp] theorem angularOneFormAt_apply (s v : ℂ) :
    angularOneFormAt s v = (dlog01 s * v).im := rfl

/-- The angular coefficient on the real horizontal basis direction. -/
@[simp] theorem angularOneFormAt_one (s : ℂ) :
    angularOneFormAt s 1 = (dlog01 s).im := by
  simp [angularOneFormAt]

/-- The angular coefficient on the real vertical basis direction. -/
@[simp] theorem angularOneFormAt_I (s : ℂ) :
    angularOneFormAt s Complex.I = (dlog01 s).re := by
  simp [angularOneFormAt, Complex.mul_im]

/-- On the punctured domain the angular form may equivalently be read from the
canonical meromorphic coefficient used by the variable Cartan connection. -/
theorem angularOneFormAt_eq_omegaCoeff
    {s : ℂ} (hs : s ∈ punctured01) (v : ℂ) :
    angularOneFormAt s v = (omegaCoeff s * v).im := by
  rw [angularOneFormAt_apply, omegaCoeff_eq_dlog01 hs]

/-- Coupled scalar connection `alpha dTheta`. -/
def coupledAngularOneFormAt (α : ℝ) (s : ℂ) : ℂ →ₗ[ℝ] ℝ :=
  α • angularOneFormAt s

@[simp] theorem coupledAngularOneFormAt_apply
    (α : ℝ) (s v : ℂ) :
    coupledAngularOneFormAt α s v =
      α * (dlog01 s * v).im := by
  simp [coupledAngularOneFormAt, angularOneFormAt]

/-- Directional derivative coefficient of the angular one-form. -/
def angularDirectionalDerivative
    (s u v : ℂ) : ℝ :=
  (omegaCoeffDeriv s * u * v).im

/-- Alternation defining the local scalar exterior derivative. -/
def angularExteriorDerivativeAt
    (s u v : ℂ) : ℝ :=
  angularDirectionalDerivative s u v -
    angularDirectionalDerivative s v u

/-- Both displayed directional derivatives arise from genuine complex
derivatives of the underlying meromorphic coefficient. -/
theorem angularDirectionalDerivative_analytic_witness
    {s : ℂ} (hs : s ∈ punctured01) (u v : ℂ) :
    HasDerivAt
        (fun t : ℂ => omegaCoeff (s + t * u) * v)
        (omegaCoeffDeriv s * u * v) 0 ∧
      HasDerivAt
        (fun t : ℂ => omegaCoeff (s + t * v) * u)
        (omegaCoeffDeriv s * v * u) 0 := by
  exact ⟨(hasDerivAt_omegaCoeff_along hs u).mul_const v,
    (hasDerivAt_omegaCoeff_along hs v).mul_const u⟩

/-- The local exterior derivative of `dTheta` vanishes. -/
@[simp] theorem angularExteriorDerivativeAt_eq_zero
    (s u v : ℂ) :
    angularExteriorDerivativeAt s u v = 0 := by
  have hcomm :
      omegaCoeffDeriv s * u * v =
        omegaCoeffDeriv s * v * u := by
    ring
  unfold angularExteriorDerivativeAt angularDirectionalDerivative
  rw [hcomm, sub_self]

/-- The scalar `U(1)` curvature coefficient of `alpha dTheta`.  The bracket
term is absent because the target Lie algebra is abelian. -/
def coupledAngularCurvatureAt
    (α : ℝ) (s u v : ℂ) : ℝ :=
  α * angularExteriorDerivativeAt s u v

/-- Every coupled angular connection is locally flat on the punctured chart. -/
@[simp] theorem coupledAngularCurvatureAt_eq_zero
    (α : ℝ) (s u v : ℂ) :
    coupledAngularCurvatureAt α s u v = 0 := by
  simp [coupledAngularCurvatureAt]

/-- The full logarithmic coefficient is circle-integrable on a small circle
around the origin. -/
theorem circleIntegrable_dlog01_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    CircleIntegrable dlog01 0 r := by
  have hpole :
      CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 0 r :=
    circleIntegrable_centerPole hr0
  have hregularBase :
      CircleIntegrable (fun z : ℂ => (z - 1)⁻¹) 0 r :=
    circleIntegrable_sub_inv_of_not_mem_closedBall hr0.le
      (one_not_mem_closedBall_zero hr1)
  have hregular :
      CircleIntegrable (fun z : ℂ => (-1 : ℂ) * (z - 1)⁻¹) 0 r := by
    simpa [smul_eq_mul] using
      (hregularBase.const_fun_smul (a := (-1 : ℂ)))
  rw [CircleIntegrable] at hpole hregular ⊢
  refine (hpole.add hregular).congr ?_
  intro t _ht
  simpa using
    (dlog01_eq_origin_pole_sub_one_pole (circleMap 0 r t)).symm

/-- The full logarithmic coefficient is circle-integrable on a small circle
around the second puncture. -/
theorem circleIntegrable_dlog01_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    CircleIntegrable dlog01 1 r := by
  have hregular :
      CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 1 r :=
    circleIntegrable_sub_inv_of_not_mem_closedBall hr0.le
      (zero_not_mem_closedBall_one hr1)
  have hpoleBase :
      CircleIntegrable (fun z : ℂ => (z - 1)⁻¹) 1 r :=
    circleIntegrable_centerPole hr0
  have hpole :
      CircleIntegrable (fun z : ℂ => (-1 : ℂ) * (z - 1)⁻¹) 1 r := by
    simpa [smul_eq_mul] using
      (hpoleBase.const_fun_smul (a := (-1 : ℂ)))
  rw [CircleIntegrable] at hregular hpole ⊢
  refine (hregular.add hpole).congr ?_
  intro t _ht
  simpa using
    (dlog01_eq_origin_pole_sub_one_pole (circleMap 1 r t)).symm

/-- Pullback of `dTheta` along Mathlib's native circle parameterization. -/
def angularCirclePullback
    (c : ℂ) (r : ℝ) (t : ℝ) : ℝ :=
  angularOneFormAt (circleMap c r t)
    (deriv (circleMap c r) t)

/-- Direct real interval integral of the angular one-form around a circle. -/
def angularCircleIntegral (c : ℂ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), angularCirclePullback c r t

/-- The direct real angular integral is exactly the imaginary part of the
complex logarithmic contour integral. -/
theorem angularCircleIntegral_eq_contourAngularPeriod
    {c : ℂ} {r : ℝ} (h : CircleIntegrable dlog01 c r) :
    angularCircleIntegral c r = contourAngularPeriod c r := by
  unfold angularCircleIntegral angularCirclePullback
    angularOneFormAt contourAngularPeriod
  rw [circleIntegral]
  simpa [smul_eq_mul, mul_comm] using
    (Complex.imCLM.intervalIntegral_comp_comm h.out)

/-- Direct angular period around the origin is `+2 pi`. -/
theorem angularCircleIntegral_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularCircleIntegral 0 r = angularPeriod originWinding := by
  rw [angularCircleIntegral_eq_contourAngularPeriod
    (circleIntegrable_dlog01_origin hr0 hr1)]
  exact contourAngularPeriod_origin hr0 hr1

/-- Direct angular period around the second puncture is `-2 pi`. -/
theorem angularCircleIntegral_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularCircleIntegral 1 r = angularPeriod oneWinding := by
  rw [angularCircleIntegral_eq_contourAngularPeriod
    (circleIntegrable_dlog01_one hr0 hr1)]
  exact contourAngularPeriod_one hr0 hr1

/-- Holonomy obtained directly from the real angular line integral. -/
def directContourU1Holonomy
    (α : ℝ) (c : ℂ) (r : ℝ) : Circle :=
  Circle.exp (α * angularCircleIntegral c r)

/-- Direct real integration agrees with the earlier imaginary-part contour
readout whenever the logarithmic coefficient is circle-integrable. -/
theorem directContourU1Holonomy_eq_contourU1Holonomy
    (α : ℝ) {c : ℂ} {r : ℝ}
    (h : CircleIntegrable dlog01 c r) :
    directContourU1Holonomy α c r =
      contourU1Holonomy α c r := by
  rw [directContourU1Holonomy, contourU1Holonomy,
    angularCircleIntegral_eq_contourAngularPeriod h]

/-- Direct analytic holonomy equals the winding-character value at the origin. -/
theorem directContourU1Holonomy_origin_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    directContourU1Holonomy α 0 r =
      u1Holonomy α originWinding := by
  rw [directContourU1Holonomy_eq_contourU1Holonomy α
      (circleIntegrable_dlog01_origin hr0 hr1),
    contourU1Holonomy_origin_eq_winding α hr0 hr1]

/-- Direct analytic holonomy equals the winding-character value at the second
puncture. -/
theorem directContourU1Holonomy_one_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    directContourU1Holonomy α 1 r =
      u1Holonomy α oneWinding := by
  rw [directContourU1Holonomy_eq_contourU1Holonomy α
      (circleIntegrable_dlog01_one hr0 hr1),
    contourU1Holonomy_one_eq_winding α hr0 hr1]

/-- Compact real-one-form, flatness, period, and holonomy packet. -/
theorem bipolar_angular_one_form_connection_packet
    (α : ℝ) {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    angularOneFormAt s v = (omegaCoeff s * v).im ∧
      angularExteriorDerivativeAt s u v = 0 ∧
      coupledAngularCurvatureAt α s u v = 0 ∧
      angularCircleIntegral 0 r = angularPeriod originWinding ∧
      angularCircleIntegral 1 r = angularPeriod oneWinding ∧
      directContourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      directContourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  exact ⟨angularOneFormAt_eq_omegaCoeff hs v,
    angularExteriorDerivativeAt_eq_zero s u v,
    coupledAngularCurvatureAt_eq_zero α s u v,
    angularCircleIntegral_origin hr0 hr1,
    angularCircleIntegral_one hr0 hr1,
    directContourU1Holonomy_origin_eq_winding α hr0 hr1,
    directContourU1Holonomy_one_eq_winding α hr0 hr1⟩

end InfoGeometry.Canonical.BipolarAngularOneFormConnection
