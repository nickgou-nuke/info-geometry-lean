import InfoGeometry.Analysis.BipolarBoundaryTrace
import Mathlib.Tactic

/-!
# Planar Hodge pair for the bipolar logarithmic coordinate

This file formalizes the exact Euclidean two-dimensional differential-form
content without invoking a global Hodge decomposition theorem.

For `s = x + i y`, the real logarithmic differential and angular differential
have coefficient pairs

`dPhi = (Phi_x, Phi_y)` and `dPsi = (-Phi_y, Phi_x)`.

Thus the angular form is the standard positively oriented Hodge rotation of the
gradient form.  This is a pointwise algebraic identity on the complement of the
two punctures; global period information is owned separately by
`BipolarWindingPeriodLattice`.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarPlanarHodgePair

/-- Real two-component coefficient carrier for planar 1-forms. -/
abbrev PlaneCovector := Fin 2 → ℝ

/-- Euclidean Hodge rotation with convention `*(a dx + b dy) = -b dx + a dy`. -/
def hodgeRotate (v : PlaneCovector) : PlaneCovector :=
  ![-v 1, v 0]

@[simp] theorem hodgeRotate_apply_zero (v : PlaneCovector) :
    hodgeRotate v 0 = -v 1 := rfl

@[simp] theorem hodgeRotate_apply_one (v : PlaneCovector) :
    hodgeRotate v 1 = v 0 := rfl

/-- Applying the planar Hodge rotation twice gives minus the original covector. -/
theorem hodgeRotate_sq (v : PlaneCovector) :
    hodgeRotate (hodgeRotate v) = -v := by
  funext i
  fin_cases i <;> simp [hodgeRotate]

/-- Coefficients of `d Phi`, where
`Phi = log |s| - log |1-s|`. -/
def dPhiCoeff (x y : ℝ) : PlaneCovector :=
  ![x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2),
    y / (x ^ 2 + y ^ 2) - y / ((x - 1) ^ 2 + y ^ 2)]

/-- Coefficients of the angular difference form
`d arg(s) - d arg(s-1)`. -/
def dPsiCoeff (x y : ℝ) : PlaneCovector :=
  ![-y / (x ^ 2 + y ^ 2) + y / ((x - 1) ^ 2 + y ^ 2),
    x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2)]

/-- Exact planar Cauchy--Riemann/Hodge relation. -/
theorem dPsiCoeff_eq_hodgeRotate_dPhiCoeff (x y : ℝ) :
    dPsiCoeff x y = hodgeRotate (dPhiCoeff x y) := by
  ext i
  fin_cases i <;> simp [dPsiCoeff, dPhiCoeff, hodgeRotate] <;> ring

/-- Conversely, one more Hodge rotation sends the angular form to `-dPhi`. -/
theorem hodgeRotate_dPsiCoeff (x y : ℝ) :
    hodgeRotate (dPsiCoeff x y) = -dPhiCoeff x y := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff, hodgeRotate_sq]

/-- The first coefficient of `dPhi` agrees with the ordinary horizontal
derivative of the real-coordinate logarithmic potential whenever the two
quadratic denominators are nonzero. -/
theorem deriv_phiXY_eq_dPhiCoeff_zero
    {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0)
    (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    deriv (fun t => BipolarBoundaryTrace.phiXY t y) x = dPhiCoeff x y 0 := by
  exact (BipolarBoundaryTrace.hasDerivAt_phiXY h0 h1).deriv

/-- On the bisector the gradient is purely normal: its tangential coefficient
vanishes. -/
theorem dPhiCoeff_half_tangent_zero (y : ℝ) :
    dPhiCoeff (1 / 2) y 1 = 0 := by
  simp [dPhiCoeff]
  ring

/-- On the bisector the normal coefficient is the positive Cauchy kernel. -/
theorem dPhiCoeff_half_normal (y : ℝ) :
    dPhiCoeff (1 / 2) y 0 = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
    nlinarith [sq_nonneg y]
  simp [dPhiCoeff]
  field_simp [ne_of_gt hpos]
  ring

/-- Therefore the angular form on the bisector is purely tangential. -/
theorem dPsiCoeff_half_normal_zero (y : ℝ) :
    dPsiCoeff (1 / 2) y 0 = 0 := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff]
  simp [hodgeRotate, dPhiCoeff_half_tangent_zero]

/-- The tangential angular coefficient on the bisector equals the same Cauchy
kernel as the normal logarithmic derivative. -/
theorem dPsiCoeff_half_tangent (y : ℝ) :
    dPsiCoeff (1 / 2) y 1 = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff]
  simp [hodgeRotate, dPhiCoeff_half_normal]

/-- Compact pointwise Hodge packet. -/
theorem planar_hodge_packet (x y : ℝ) :
    dPsiCoeff x y = hodgeRotate (dPhiCoeff x y) ∧
      hodgeRotate (dPsiCoeff x y) = -dPhiCoeff x y := by
  exact ⟨dPsiCoeff_eq_hodgeRotate_dPhiCoeff x y,
    hodgeRotate_dPsiCoeff x y⟩

end InfoGeometry.Analysis.BipolarPlanarHodgePair
