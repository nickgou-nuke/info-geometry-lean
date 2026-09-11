import InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarU1PeriodHolonomy
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge

/-!
# Actual contour periods and the central half-Cartan representation

The matrix below is computed from the actual Mathlib circle integral, not
from an assumed period or a disk indicator.  The enclosure theorem then
identifies it with the repository's existing `spinHolonomy`.

On the whole existing integer-pair carrier, the two half-exponential entries
coincide, their square is one, and the resulting matrix is central.  Thus the
adjoint action is trivial for every integer pair, not just the generators.

This finite exponential readout is not a construction of parallel transport
for a smooth principal bundle.  In particular no path-ordered-exponential or
arbitrary-loop classification theorem is silently inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarContourSpinHolonomy

open scoped Interval Real
open Complex Metric
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarElementaryContourPeriods
open InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarU1PeriodHolonomy

open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge

/-- Opposite half-weights agree because the full period exponentiates to one. -/
theorem exp_neg_half_period_eq_exp_half (w : WindingPair) :
    Complex.exp (-circulationPeriod w / 2) =
      Complex.exp (circulationPeriod w / 2) := by
  calc
    Complex.exp (-circulationPeriod w / 2) =
        Complex.exp (-circulationPeriod w / 2) *
          Complex.exp (circulationPeriod w) := by
            rw [exp_circulationPeriod, mul_one]
    _ = Complex.exp (circulationPeriod w / 2) := by
      rw [← Complex.exp_add]
      congr 1
      ring

/-- Every half-period phase is a square root of one. -/
theorem exp_half_period_mul_self (w : WindingPair) :
    Complex.exp (circulationPeriod w / 2) *
      Complex.exp (circulationPeriod w / 2) = 1 := by
  rw [← Complex.exp_add]
  have harg : circulationPeriod w / 2 + circulationPeriod w / 2 =
      circulationPeriod w := by ring
  rw [harg]
  exact exp_circulationPeriod w

/-- Centrality on the full integer-pair carrier, not only on elementary loops. -/
theorem spinHolonomy_eq_scalar_one (w : WindingPair) :
    spinHolonomy w = Complex.exp (circulationPeriod w / 2) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHolonomy, Matrix.smul_apply, exp_neg_half_period_eq_exp_half]

/-- The only possible half-Cartan period matrices are the two central signs. -/
theorem spinHolonomy_eq_one_or_neg_one (w : WindingPair) :
    spinHolonomy w = (1 : M2C) ∨ spinHolonomy w = -(1 : M2C) := by
  have hfactor :
      (Complex.exp (circulationPeriod w / 2) - 1) *
        (Complex.exp (circulationPeriod w / 2) + 1) = 0 := by
    calc
      _ = Complex.exp (circulationPeriod w / 2) *
          Complex.exp (circulationPeriod w / 2) - 1 := by ring
      _ = 0 := by rw [exp_half_period_mul_self, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    rw [spinHolonomy_eq_scalar_one, sub_eq_zero.mp h, one_smul]
  · right
    have hphase : Complex.exp (circulationPeriod w / 2) = -1 :=
      eq_neg_of_add_eq_zero_left h
    rw [spinHolonomy_eq_scalar_one, hphase]
    simp

/-- Every installed integer period is invisible in the adjoint matrix action.
The second factor is the inverse because the period matrix is an involution. -/
theorem spinHolonomy_adjoint_trivial_all (w : WindingPair) (X : M2C) :
    spinHolonomy w * X * spinHolonomy w = X := by
  rcases spinHolonomy_eq_one_or_neg_one w with h | h <;> simp [h]

/-- The two-turn law holds for every integer pair. -/
theorem spinHolonomy_sq_all (w : WindingPair) :
    spinHolonomy w * spinHolonomy w = (1 : M2C) := by
  simpa only [mul_one] using spinHolonomy_adjoint_trivial_all w (1 : M2C)

/-- The central spin sign equals the existing half-coupled scalar circle
character, acting by scalar multiplication on the spinor carrier. -/
theorem spinHolonomy_eq_half_u1_scalar (w : WindingPair) :
    spinHolonomy w = (u1Holonomy (1 / 2 : ℝ) w : ℂ) • (1 : M2C) := by
  have hphase : (u1Holonomy (1 / 2 : ℝ) w : ℂ) =
      Complex.exp (circulationPeriod w / 2) := by
    rw [coe_u1Holonomy_eq_exp_circulation]
    congr 1
    push_cast
    ring
  rw [spinHolonomy_eq_scalar_one, hphase]

/-- Half-Cartan exponential readout of the actual full circle integral.
Only the theorems with explicit pole-avoidance hypotheses interpret this as a
regular contour period; totalization at singular inputs is not physical data. -/
def contourSpinHolonomy (c : ℂ) (r : ℝ) : M2C :=
  !![Complex.exp ((∮ z in C(c, r), dlog01 z) / 2), 0;
     0, Complex.exp (-(∮ z in C(c, r), dlog01 z) / 2)]

/-- Determinant one follows from the opposite exponential weights alone. -/
theorem contourSpinHolonomy_det (c : ℂ) (r : ℝ) :
    Matrix.det (contourSpinHolonomy c r) = 1 := by
  rw [Matrix.det_fin_two]
  change Complex.exp ((∮ z in C(c, r), dlog01 z) / 2) *
    Complex.exp (-(∮ z in C(c, r), dlog01 z) / 2) - 0 * 0 = 1
  rw [zero_mul, sub_zero, ← Complex.exp_add]
  have harg : (∮ z in C(c, r), dlog01 z) / 2 +
      -(∮ z in C(c, r), dlog01 z) / 2 = 0 := by ring
  rw [harg, Complex.exp_zero]

/-- The analytic integral, rather than an assumed period equality, supplies
the bridge to the existing half-Cartan representation. -/
theorem contourSpinHolonomy_eq_winding
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    contourSpinHolonomy c r = spinHolonomy (circleEnclosurePair c r) := by
  unfold contourSpinHolonomy
  rw [circleIntegral_dlog01_eq_circulationPeriod hr h0 h1]
  rfl

/-- The corresponding scalar character agrees on every regular circle. -/
theorem contourU1Holonomy_eq_winding
    (α : ℝ) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    contourU1Holonomy α c r = u1Holonomy α (circleEnclosurePair c r) := by
  rw [contourU1Holonomy, contourAngularPeriod,
    circleIntegral_dlog01_eq_circulationPeriod hr h0 h1,
    circulationPeriod_im_eq_angularPeriod, u1Holonomy_apply]

/-- Exact comparison between the matrix and scalar half-coupled contour readouts. -/
theorem contourSpinHolonomy_eq_half_u1_scalar
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    contourSpinHolonomy c r =
      (contourU1Holonomy (1 / 2 : ℝ) c r : ℂ) • (1 : M2C) := by
  rw [contourSpinHolonomy_eq_winding hr h0 h1,
    contourU1Holonomy_eq_winding (1 / 2 : ℝ) hr h0 h1]
  exact spinHolonomy_eq_half_u1_scalar _

/-- The actual small origin-circle integral gives the nontrivial central sign. -/
theorem contourSpinHolonomy_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourSpinHolonomy 0 r = -(1 : M2C) := by
  unfold contourSpinHolonomy
  rw [circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1]
  exact spinHolonomy_origin

/-- The opposite scalar period gives the same half-Cartan central sign. -/
theorem contourSpinHolonomy_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourSpinHolonomy 1 r = -(1 : M2C) := by
  unfold contourSpinHolonomy
  rw [circleIntegral_dlog01_one_eq_circulationPeriod hr0 hr1]
  exact spinHolonomy_one

/-- A circle enclosing both poles has the identity matrix readout. -/
theorem contourSpinHolonomy_of_both_inside
    {c : ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ball c r) (h1 : (1 : ℂ) ∈ ball c r) :
    contourSpinHolonomy c r = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [contourSpinHolonomy, circleIntegral_dlog01_of_both_inside h0 h1]

/-- All regular circle half-Cartan matrices are involutions. -/
theorem contourSpinHolonomy_sq
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    contourSpinHolonomy c r * contourSpinHolonomy c r = (1 : M2C) := by
  simp only [contourSpinHolonomy_eq_winding hr h0 h1]
  exact spinHolonomy_sq_all _

/-- Every regular circle readout acts trivially on matrices by conjugation. -/
theorem contourSpinHolonomy_adjoint_trivial
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) (X : M2C) :
    contourSpinHolonomy c r * X * contourSpinHolonomy c r = X := by
  simp only [contourSpinHolonomy_eq_winding hr h0 h1]
  exact spinHolonomy_adjoint_trivial_all _ X

/-- The same actual elementary contour changes the sign of a spinor. -/
theorem contourSpinHolonomy_origin_spinor
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ψ : Spinor2) :
    spinorAction (contourSpinHolonomy 0 r) ψ = -ψ := by
  rw [contourSpinHolonomy_origin hr0 hr1]
  exact spinorAction_neg_one ψ

/-- Integral scalar coupling is trivial for all regular circles. -/
theorem contourU1Holonomy_integer_coupling
    (k : ℤ) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    contourU1Holonomy (k : ℝ) c r = 1 := by
  rw [contourU1Holonomy_eq_winding (k : ℝ) hr h0 h1]
  exact u1Holonomy_integer_coupling k _

end InfoGeometry.Canonical.BipolarContourSpinHolonomy
