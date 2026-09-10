import InfoGeometry.Canonical.BipolarAngularOneFormConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarComplexCartanLine
import InfoGeometry.Canonical.BipolarContourSpinHolonomy
import InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge
import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import Mathlib.Tactic

/-!
# Native Apollonius operator connection

This module is the public Layer-3 interface for the bipolar/Apollonius theorem
DAG.  It reuses the existing theorem owners rather than introducing parallel
cross-ratio, Pauli, contour-integral, or exterior-algebra definitions.

For a point `s` of the twice-punctured plane, the branch-independent complex
Cartan connection is

`A_s(v) = (dlog01(s) * v / 2) • sigma3`.

Its values lie in the trace-zero complex Cartan line.  Its exterior derivative
and operator self-wedge vanish separately, hence its curvature vanishes.  On a
compatible principal-log chart it is the left Maurer--Cartan form
`G^{-1} dG` of the actual half-log lift.

The real angular component is the genuine real-linear one-form

`alpha dTheta_s(v) = alpha * Im(dlog01(s) * v)`.

Direct Mathlib circle integration gives the periods `+2 pi alpha` and
`-2 pi alpha`.  The half-Cartan matrix readout gives the central sign `-I` on
each elementary puncture circle and `I` on a circle enclosing both punctures.

The compact Cartan coefficient defines a repository-native `OpDerivation` and
has the two parabolic root matrices as eigenoperators with weights `+i` and
`-i`.

No distributional extension through the punctures, magnetic-field equation,
principal-bundle parallel transport, or microscopic Aharonov--Bohm model is
asserted.  Those are additional realization layers, not consequences of local
flatness on the punctured domain.
-/

noncomputable section

namespace InfoGeometry.Connection.ApolloniusOperatorConnection

open scoped Interval Real
open Complex Metric Set
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Canonical.BipolarAngularOneFormConnection
open InfoGeometry.Canonical.BipolarComplexCartanLine
open InfoGeometry.Canonical.BipolarContourSpinHolonomy
open InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.Information.ModularSurprisalDerivationBridge
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- The twice-punctured complex plane as a subtype. -/
abbrev ApolloniusPoint := {s : ℂ // s ∈ punctured01}

/-! ## 1. Branch-independent complex Cartan connection -/

/-- Point-dependent operator-valued one-form on the punctured plane. -/
def operatorConnectionAt (s : ApolloniusPoint) :
    Op1Form ℂ ℂ Matrix2C :=
  variableCartanConnection (s : ℂ)

/-- The public connection is exactly one half of `dlog q`, valued in `sigma3`. -/
@[simp] theorem operatorConnectionAt_apply
    (s : ApolloniusPoint) (v : ℂ) :
    operatorConnectionAt s v =
      ((dlog01 (s : ℂ) * v) / 2) • σ3c := by
  simpa [operatorConnectionAt] using
    (variableCartanConnection_eq_dlog01
      (s := (s : ℂ)) s.property v)

/-- Every connection value lies in the one-dimensional complex Cartan line. -/
theorem operatorConnectionAt_value_mem_cartanLine
    (s : ApolloniusPoint) (v : ℂ) :
    operatorConnectionAt s v ∈ cartanLine := by
  rw [operatorConnectionAt_apply, cartanLine]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton σ3c))

/-- Every connection value is trace zero. -/
theorem operatorConnectionAt_value_trace_zero
    (s : ApolloniusPoint) (v : ℂ) :
    Matrix.trace (operatorConnectionAt s v) = 0 := by
  change operatorConnectionAt s v ∈ traceZeroMatrices
  exact cartanLine_le_traceZeroMatrices
    (operatorConnectionAt_value_mem_cartanLine s v)

/-- The actual analytic half-log differential gives the local pure-gauge
factorization `G^{-1} dG = A`. -/
theorem operatorConnectionAt_eq_local_pureGauge
    (s : ApolloniusPoint) (v : ℂ) :
    halfLogLiftInv (s : ℂ) *
        halfLogLiftAnalyticDifferential (s : ℂ) v =
      operatorConnectionAt s v := by
  simpa [operatorConnectionAt] using
    (halfLogLift_local_pure_gauge s.property v)

/-- On the principal-log chart, the displayed matrix differential is the
actual entrywise derivative of the half-log lift. -/
theorem operatorConnectionAt_analytic_pureGauge
    (s : ApolloniusPoint)
    (hslit : crossRatio01 (s : ℂ) ∈ Complex.slitPlane)
    (v : ℂ) (i j : Fin 2) :
    HasDerivAt
        (fun t : ℂ => halfLogLift ((s : ℂ) + t * v) i j)
        (halfLogLiftAnalyticDifferential (s : ℂ) v i j) 0 ∧
      halfLogLiftInv (s : ℂ) *
          halfLogLiftAnalyticDifferential (s : ℂ) v =
        operatorConnectionAt s v := by
  simpa [operatorConnectionAt] using
    (bipolar_half_log_pure_gauge_packet
      s.property hslit v i j)

/-! ## 2. Exterior derivative, self-wedge, and curvature -/

/-- Alternation of the actual directional derivative of the connection. -/
def operatorExteriorDerivativeAt
    (s : ApolloniusPoint) (u v : ℂ) : Matrix2C :=
  variableExteriorDerivativeAt (s : ℂ) u v

/-- Operator self-wedge evaluated on two tangent vectors. -/
def operatorWedgeAt
    (s : ApolloniusPoint) (u v : ℂ) : Matrix2C :=
  wedge (operatorConnectionAt s) (operatorConnectionAt s) u v

/-- Curvature `F = dA + A wedge A`. -/
def operatorCurvatureAt
    (s : ApolloniusPoint) (u v : ℂ) : Matrix2C :=
  operatorExteriorDerivativeAt s u v + operatorWedgeAt s u v

/-- The exterior derivative vanishes because the derivative coefficient is
symmetric in the two complex tangent directions. -/
@[simp] theorem operatorExteriorDerivativeAt_eq_zero
    (s : ApolloniusPoint) (u v : ℂ) :
    operatorExteriorDerivativeAt s u v = 0 := by
  simp [operatorExteriorDerivativeAt]

/-- The entire form-level self-wedge vanishes because all values lie in the
same abelian Cartan line. -/
theorem operatorConnectionAt_selfWedge_zero
    (s : ApolloniusPoint) :
    wedge (operatorConnectionAt s) (operatorConnectionAt s) = 0 := by
  simpa [operatorConnectionAt] using
    (variableCartanConnection_selfWedge_zero (s : ℂ))

/-- The commutator part of the curvature vanishes pointwise. -/
@[simp] theorem operatorWedgeAt_eq_zero
    (s : ApolloniusPoint) (u v : ℂ) :
    operatorWedgeAt s u v = 0 := by
  change wedge (variableCartanConnection (s : ℂ))
      (variableCartanConnection (s : ℂ)) u v = 0
  rw [variableCartanConnection_selfWedge_zero]
  rfl

/-- Nonconstant Maurer--Cartan equation on the punctured domain. -/
@[simp] theorem operatorCurvatureAt_eq_zero
    (s : ApolloniusPoint) (u v : ℂ) :
    operatorCurvatureAt s u v = 0 := by
  simp [operatorCurvatureAt]

/-! ## 3. Compact Cartan inner derivation -/

/-- The compact Cartan coefficient as a native complex-linear Leibniz
derivation of the full matrix algebra. -/
def circularOpDerivation : OpDerivation ℂ Matrix2C where
  toLinearMap := adK_algebra (R := ℂ) Kcirc
  leibniz' := by
    intro X Y
    simpa using
      adK_algebra_is_derivation (R := ℂ) Kcirc X Y

@[simp] theorem circularOpDerivation_apply (X : Matrix2C) :
    circularOpDerivation X = Kcirc * X - X * Kcirc :=
  rfl

/-- Native Leibniz law for the compact derivation. -/
theorem circularOpDerivation_leibniz (X Y : Matrix2C) :
    circularOpDerivation (X * Y) =
      circularOpDerivation X * Y + X * circularOpDerivation Y := by
  exact circularOpDerivation.leibniz X Y

/-- Positive parabolic root weight `+i`. -/
@[simp] theorem circularOpDerivation_sigmaPlus :
    circularOpDerivation σPlus = Complex.I • σPlus := by
  rw [circularOpDerivation_apply]
  exact Kcirc_comm_sigmaPlus

/-- Negative parabolic root weight `-i`. -/
@[simp] theorem circularOpDerivation_sigmaMinus :
    circularOpDerivation σMinus = (-Complex.I) • σMinus := by
  rw [circularOpDerivation_apply]
  exact Kcirc_comm_sigmaMinus

/-- The compact derivation annihilates the whole Cartan line. -/
theorem circularOpDerivation_eq_zero_of_mem_cartanLine
    {X : Matrix2C} (hX : X ∈ cartanLine) :
    circularOpDerivation X = 0 := by
  rw [circularOpDerivation_apply]
  exact cartanLine_commutator_zero Kcirc_mem_cartanLine hX

/-! ## 4. Real angular connection and direct periods -/

/-- Real scalar connection `alpha dTheta` on the punctured plane. -/
def planarAngularConnectionAt
    (α : ℝ) (s : ApolloniusPoint) : ℂ →ₗ[ℝ] ℝ :=
  α • angularOneFormAt (s : ℂ)

@[simp] theorem planarAngularConnectionAt_apply
    (α : ℝ) (s : ApolloniusPoint) (v : ℂ) :
    planarAngularConnectionAt α s v =
      α * (dlog01 (s : ℂ) * v).im := by
  simp [planarAngularConnectionAt, angularOneFormAt]

/-- Local curvature coefficient of the real angular connection. -/
def planarAngularCurvatureAt
    (α : ℝ) (s : ApolloniusPoint) (u v : ℂ) : ℝ :=
  coupledAngularCurvatureAt α (s : ℂ) u v

/-- The scalar angular connection is locally flat. -/
@[simp] theorem planarAngularCurvatureAt_eq_zero
    (α : ℝ) (s : ApolloniusPoint) (u v : ℂ) :
    planarAngularCurvatureAt α s u v = 0 := by
  simp [planarAngularCurvatureAt]

/-- Direct coupled line integral `alpha integral dTheta` around a circle. -/
def coupledAngularCircleIntegral
    (α : ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  α * angularCircleIntegral c r

/-- The elementary origin circle has coupled period `+2 pi alpha`. -/
theorem coupledAngularCircleIntegral_origin
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    coupledAngularCircleIntegral α 0 r = α * (2 * Real.pi) := by
  unfold coupledAngularCircleIntegral
  rw [angularCircleIntegral_origin hr0 hr1, angularPeriod_origin]

/-- The elementary circle around `1` has coupled period `-2 pi alpha`. -/
theorem coupledAngularCircleIntegral_one
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    coupledAngularCircleIntegral α 1 r = α * (-(2 * Real.pi)) := by
  unfold coupledAngularCircleIntegral
  rw [angularCircleIntegral_one hr0 hr1, angularPeriod_one]

/-- Direct circle-valued holonomy of the real angular connection. -/
def planarU1Holonomy
    (α : ℝ) (c : ℂ) (r : ℝ) : Circle :=
  directContourU1Holonomy α c r

/-- Direct analytic holonomy agrees with the winding character at `0`. -/
theorem planarU1Holonomy_origin_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    planarU1Holonomy α 0 r = u1Holonomy α originWinding := by
  simpa [planarU1Holonomy] using
    (directContourU1Holonomy_origin_eq_winding α hr0 hr1)

/-- Direct analytic holonomy agrees with the winding character at `1`. -/
theorem planarU1Holonomy_one_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    planarU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  simpa [planarU1Holonomy] using
    (directContourU1Holonomy_one_eq_winding α hr0 hr1)

/-! ## 5. Central half-Cartan contour holonomy -/

/-- Matrix half-Cartan readout of the actual logarithmic circle integral. -/
def spinContourHolonomy (c : ℂ) (r : ℝ) : Matrix2C :=
  contourSpinHolonomy c r

/-- Every contour readout has determinant one. -/
@[simp] theorem spinContourHolonomy_det (c : ℂ) (r : ℝ) :
    Matrix.det (spinContourHolonomy c r) = 1 := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_det c r)

/-- The actual elementary origin circle gives the central sign `-I`. -/
theorem spinContourHolonomy_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    spinContourHolonomy 0 r = -(1 : Matrix2C) := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_origin hr0 hr1)

/-- The actual elementary circle around `1` gives the same central sign. -/
theorem spinContourHolonomy_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    spinContourHolonomy 1 r = -(1 : Matrix2C) := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_one hr0 hr1)

/-- A circle containing both punctures has trivial half-Cartan readout. -/
theorem spinContourHolonomy_of_both_inside
    {c : ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ball c r) (h1 : (1 : ℂ) ∈ ball c r) :
    spinContourHolonomy c r = (1 : Matrix2C) := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_of_both_inside h0 h1)

/-- Every regular-circle half-Cartan readout is an involution. -/
theorem spinContourHolonomy_sq
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    spinContourHolonomy c r * spinContourHolonomy c r =
      (1 : Matrix2C) := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_sq hr h0 h1)

/-- Every regular-circle readout acts trivially in the adjoint matrix
representation. -/
theorem spinContourHolonomy_adjoint_trivial
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r)
    (X : Matrix2C) :
    spinContourHolonomy c r * X * spinContourHolonomy c r = X := by
  simpa [spinContourHolonomy] using
    (contourSpinHolonomy_adjoint_trivial hr h0 h1 X)

/-! ## 6. Complete Layer-3 packet -/

/-- Public closure theorem for the intrinsic operator-connection layer. -/
theorem apollonius_operator_connection_packet
    (α : ℝ) (s : ApolloniusPoint) (u v : ℂ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    operatorConnectionAt s v =
        ((dlog01 (s : ℂ) * v) / 2) • σ3c ∧
      Matrix.trace (operatorConnectionAt s v) = 0 ∧
      operatorExteriorDerivativeAt s u v = 0 ∧
      operatorWedgeAt s u v = 0 ∧
      operatorCurvatureAt s u v = 0 ∧
      circularOpDerivation σPlus = Complex.I • σPlus ∧
      circularOpDerivation σMinus = (-Complex.I) • σMinus ∧
      coupledAngularCircleIntegral α 0 r = α * (2 * Real.pi) ∧
      coupledAngularCircleIntegral α 1 r = α * (-(2 * Real.pi)) ∧
      spinContourHolonomy 0 r = -(1 : Matrix2C) ∧
      spinContourHolonomy 1 r = -(1 : Matrix2C) := by
  exact ⟨operatorConnectionAt_apply s v,
    operatorConnectionAt_value_trace_zero s v,
    operatorExteriorDerivativeAt_eq_zero s u v,
    operatorWedgeAt_eq_zero s u v,
    operatorCurvatureAt_eq_zero s u v,
    circularOpDerivation_sigmaPlus,
    circularOpDerivation_sigmaMinus,
    coupledAngularCircleIntegral_origin α hr0 hr1,
    coupledAngularCircleIntegral_one α hr0 hr1,
    spinContourHolonomy_origin hr0 hr1,
    spinContourHolonomy_one hr0 hr1⟩

end InfoGeometry.Connection.ApolloniusOperatorConnection
