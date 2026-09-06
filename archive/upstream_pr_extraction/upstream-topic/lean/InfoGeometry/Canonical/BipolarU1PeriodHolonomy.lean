import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-!
# Scalar U(1) period holonomy of the bipolar angular form

The logarithmic differential has complex period

`circulationPeriod w = 2π i (m - n)`

on the explicit winding carrier `WindingPair = ℤ × ℤ`.  Its imaginary part is
the real angular period of `dθ`:

`angularPeriod w = 2π (m - n)`.

For a real coupling `α`, exponentiating `α * angularPeriod w` with Mathlib's
native circle exponential gives an additive character

`u1Holonomy α : AddChar WindingPair Circle`.

This is the exact finite holonomy representation determined by the installed
winding lattice and the genuine elementary contour integrals.  Unit integral
coupling is trivial because the angular periods are integral multiples of
`2π`; half coupling gives the nontrivial order-two phase on an elementary
puncture winding.

No arbitrary-loop classification, smooth principal bundle, distributional
curvature, electromagnetic field equation, or microscopic Aharonov--Bohm
realization is asserted.  Such interpretations require additional geometric
and physical data.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarU1PeriodHolonomy

open scoped Interval Real
open Complex Metric
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarElementaryContourPeriods

/-- Real angular period detected by the bipolar residue pairing. -/
def angularPeriod (w : WindingPair) : ℝ :=
  (residueWinding w : ℝ) * (2 * Real.pi)

/-- The angular period as a genuine additive homomorphism. -/
def angularPeriodHom : WindingPair →+ ℝ where
  toFun := angularPeriod
  map_zero' := by
    change (((0 - 0 : ℤ) : ℝ) * (2 * Real.pi)) = 0
    norm_num
  map_add' u v := by
    rcases u with ⟨u₀, u₁⟩
    rcases v with ⟨v₀, v₁⟩
    change
      ((((u₀ + v₀) - (u₁ + v₁) : ℤ) : ℝ) * (2 * Real.pi)) =
        (((u₀ - u₁ : ℤ) : ℝ) * (2 * Real.pi)) +
          (((v₀ - v₁ : ℤ) : ℝ) * (2 * Real.pi))
    push_cast
    ring

@[simp] theorem angularPeriodHom_apply (w : WindingPair) :
    angularPeriodHom w = angularPeriod w := rfl

@[simp] theorem angularPeriod_zero : angularPeriod 0 = 0 := by
  exact angularPeriodHom.map_zero

/-- Additivity of the angular period on winding pairs. -/
theorem angularPeriod_add (u v : WindingPair) :
    angularPeriod (u + v) = angularPeriod u + angularPeriod v := by
  exact angularPeriodHom.map_add u v

@[simp] theorem angularPeriod_origin :
    angularPeriod originWinding = 2 * Real.pi := by
  norm_num [angularPeriod, originWinding, residueWinding]

@[simp] theorem angularPeriod_one :
    angularPeriod oneWinding = -(2 * Real.pi) := by
  norm_num [angularPeriod, oneWinding, residueWinding]

@[simp] theorem angularPeriod_diagonal (n : ℤ) :
    angularPeriod (diagonalWinding n) = 0 := by
  simp [angularPeriod, diagonalWinding, residueWinding]

/-- The complex logarithmic period is `i` times the real angular period. -/
theorem circulationPeriod_eq_angularPeriod_mul_I (w : WindingPair) :
    circulationPeriod w = (angularPeriod w : ℂ) * Complex.I := by
  rcases w with ⟨m, n⟩
  simp only [circulationPeriod, angularPeriod, residueWinding]
  push_cast
  ring

/-- The angular period is the imaginary part of the complex logarithmic period. -/
theorem circulationPeriod_im_eq_angularPeriod (w : WindingPair) :
    (circulationPeriod w).im = angularPeriod w := by
  rw [circulationPeriod_eq_angularPeriod_mul_I]
  simp

/-- The logarithmic circulation period has vanishing real part. -/
theorem circulationPeriod_re_eq_zero (w : WindingPair) :
    (circulationPeriod w).re = 0 := by
  rw [circulationPeriod_eq_angularPeriod_mul_I]
  simp

/-- Imaginary-part readout of the actual logarithmic contour integral. -/
def contourAngularPeriod (c : ℂ) (r : ℝ) : ℝ :=
  (∮ z in C(c, r), dlog01 z).im

/-- The small positive circle around `0` has angular period `+2π`. -/
theorem contourAngularPeriod_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourAngularPeriod 0 r = angularPeriod originWinding := by
  rw [contourAngularPeriod,
    circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1,
    circulationPeriod_im_eq_angularPeriod]

/-- The small positive circle around `1` has angular period `-2π`. -/
theorem contourAngularPeriod_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourAngularPeriod 1 r = angularPeriod oneWinding := by
  rw [contourAngularPeriod,
    circleIntegral_dlog01_one_eq_circulationPeriod hr0 hr1,
    circulationPeriod_im_eq_angularPeriod]

/-- Coupled angular period `α ∮ dθ` as an additive homomorphism. -/
def coupledAngularPeriodHom (α : ℝ) : WindingPair →+ ℝ where
  toFun w := α * angularPeriod w
  map_zero' := by
    rw [angularPeriod_zero, mul_zero]
  map_add' u v := by
    rw [angularPeriod_add, mul_add]

@[simp] theorem coupledAngularPeriodHom_apply
    (α : ℝ) (w : WindingPair) :
    coupledAngularPeriodHom α w = α * angularPeriod w := rfl

/-- Native unit-circle holonomy character of the coupled angular period. -/
def u1Holonomy (α : ℝ) : AddChar WindingPair Circle where
  toFun w := Circle.exp (coupledAngularPeriodHom α w)
  map_zero_eq_one' := by
    simp
  map_add_eq_mul' u v := by
    rw [(coupledAngularPeriodHom α).map_add, Circle.exp_add]

@[simp] theorem u1Holonomy_apply (α : ℝ) (w : WindingPair) :
    u1Holonomy α w = Circle.exp (α * angularPeriod w) := rfl

/-- Holonomy is multiplicative under addition of winding classes. -/
theorem u1Holonomy_add (α : ℝ) (u v : WindingPair) :
    u1Holonomy α (u + v) = u1Holonomy α u * u1Holonomy α v := by
  exact (u1Holonomy α).map_add_eq_mul u v

@[simp] theorem u1Holonomy_zero (α : ℝ) :
    u1Holonomy α 0 = 1 := by
  exact (u1Holonomy α).map_zero_eq_one

/-- Holonomy on the first elementary winding. -/
theorem u1Holonomy_origin (α : ℝ) :
    u1Holonomy α originWinding = Circle.exp (α * (2 * Real.pi)) := by
  rw [u1Holonomy_apply, angularPeriod_origin]

/-- Holonomy on the second elementary winding. -/
theorem u1Holonomy_one (α : ℝ) :
    u1Holonomy α oneWinding = Circle.exp (α * (-(2 * Real.pi))) := by
  rw [u1Holonomy_apply, angularPeriod_one]

/-- Opposite residue signs give mutually inverse elementary holonomies. -/
theorem u1Holonomy_one_eq_inv_origin (α : ℝ) :
    u1Holonomy α oneWinding = (u1Holonomy α originWinding)⁻¹ := by
  rw [u1Holonomy_one, u1Holonomy_origin]
  have harg : α * (-(2 * Real.pi)) = -(α * (2 * Real.pi)) := by
    ring
  rw [harg, Circle.exp_neg]

/-- Diagonal winding is invisible to the residue-difference connection. -/
@[simp] theorem u1Holonomy_diagonal (α : ℝ) (n : ℤ) :
    u1Holonomy α (diagonalWinding n) = 1 := by
  rw [u1Holonomy_apply, angularPeriod_diagonal, mul_zero, Circle.exp_zero]

/-- Complex-valued form of the circle character: exponentiation of the coupled
complex logarithmic period. -/
theorem coe_u1Holonomy_eq_exp_circulation
    (α : ℝ) (w : WindingPair) :
    (u1Holonomy α w : ℂ) =
      Complex.exp ((α : ℂ) * circulationPeriod w) := by
  rw [u1Holonomy_apply, Circle.coe_exp,
    circulationPeriod_eq_angularPeriod_mul_I]
  congr 1
  push_cast
  ring

/-- The native circle exponential closes after one full turn. -/
theorem circle_exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
  apply Circle.ext
  simpa [Circle.coe_exp] using
    (Complex.exp_int_mul_two_pi_mul_I (1 : ℤ))

/-- Unit coupling kills every integral bipolar angular period. -/
theorem u1Holonomy_unit_coupling (w : WindingPair) :
    u1Holonomy 1 w = 1 := by
  apply Circle.ext
  rw [coe_u1Holonomy_eq_exp_circulation]
  simpa using exp_circulationPeriod w

/-- Every integral coupling gives trivial holonomy on the integral winding
lattice. -/
theorem u1Holonomy_integer_coupling (k : ℤ) (w : WindingPair) :
    u1Holonomy (k : ℝ) w = 1 := by
  have hunit : Circle.exp (angularPeriod w) = 1 := by
    simpa [u1Holonomy_apply] using u1Holonomy_unit_coupling w
  calc
    u1Holonomy (k : ℝ) w =
        Circle.exp ((k : ℝ) * angularPeriod w) := rfl
    _ = Circle.exp (angularPeriod w) ^ k := by
      exact Circle.exp_intCast_mul (angularPeriod w) k
    _ = 1 := by simp [hunit]

/-- The canonical order-two phase obtained from half a full turn. -/
def halfFluxPhase : Circle :=
  Circle.exp Real.pi

/-- Half coupling gives the order-two phase on the first elementary winding. -/
theorem u1Holonomy_half_origin :
    u1Holonomy (1 / 2 : ℝ) originWinding = halfFluxPhase := by
  rw [u1Holonomy_origin]
  unfold halfFluxPhase
  congr 1
  ring

/-- The half-turn phase is genuinely nontrivial. -/
theorem halfFluxPhase_ne_one : halfFluxPhase ≠ 1 := by
  exact Circle.exp_pi_ne_one

/-- Hence the half-coupled elementary holonomy is nontrivial. -/
theorem u1Holonomy_half_origin_ne_one :
    u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 := by
  rw [u1Holonomy_half_origin]
  exact halfFluxPhase_ne_one

/-- The half-turn phase has order two. -/
theorem halfFluxPhase_sq : halfFluxPhase * halfFluxPhase = 1 := by
  rw [halfFluxPhase, ← Circle.exp_add]
  have harg : Real.pi + Real.pi = 2 * Real.pi := by ring
  rw [harg, circle_exp_two_pi]

/-- Two half-coupled turns around the first puncture close. -/
theorem u1Holonomy_half_origin_sq :
    u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 := by
  rw [u1Holonomy_half_origin, halfFluxPhase_sq]

/-- Holonomy computed from the actual logarithmic contour integral. -/
def contourU1Holonomy (α : ℝ) (c : ℂ) (r : ℝ) : Circle :=
  Circle.exp (α * contourAngularPeriod c r)

/-- Analytic and algebraic holonomy agree for a small circle around `0`. -/
theorem contourU1Holonomy_origin_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourU1Holonomy α 0 r = u1Holonomy α originWinding := by
  rw [contourU1Holonomy, contourAngularPeriod_origin hr0 hr1,
    u1Holonomy_apply]

/-- Analytic and algebraic holonomy agree for a small circle around `1`. -/
theorem contourU1Holonomy_one_eq_winding
    (α : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourU1Holonomy α 1 r = u1Holonomy α oneWinding := by
  rw [contourU1Holonomy, contourAngularPeriod_one hr0 hr1,
    u1Holonomy_apply]

/-- Unit-coupled elementary contour holonomies are trivial. -/
theorem contourU1Holonomy_unit_elementary
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourU1Holonomy 1 0 r = 1 ∧
      contourU1Holonomy 1 1 r = 1 := by
  exact ⟨by
      rw [contourU1Holonomy_origin_eq_winding 1 hr0 hr1,
        u1Holonomy_unit_coupling],
    by
      rw [contourU1Holonomy_one_eq_winding 1 hr0 hr1,
        u1Holonomy_unit_coupling]⟩

/-- Half-coupled origin contour has nontrivial order-two holonomy. -/
theorem contourU1Holonomy_half_origin_ne_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    contourU1Holonomy (1 / 2 : ℝ) 0 r ≠ 1 := by
  rw [contourU1Holonomy_origin_eq_winding (1 / 2 : ℝ) hr0 hr1]
  exact u1Holonomy_half_origin_ne_one

/-- Compact scalar period-holonomy packet. -/
theorem bipolar_u1_period_holonomy_packet
    (α : ℝ) (w : WindingPair)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circulationPeriod w = (angularPeriod w : ℂ) * Complex.I ∧
      (u1Holonomy α (originWinding + oneWinding) = 1) ∧
      contourU1Holonomy α 0 r = u1Holonomy α originWinding ∧
      contourU1Holonomy α 1 r = u1Holonomy α oneWinding ∧
      u1Holonomy 1 w = 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding ≠ 1 ∧
      u1Holonomy (1 / 2 : ℝ) originWinding *
        u1Holonomy (1 / 2 : ℝ) originWinding = 1 := by
  exact ⟨circulationPeriod_eq_angularPeriod_mul_I w,
    by
      rw [u1Holonomy_add, u1Holonomy_one_eq_inv_origin]
      simp,
    contourU1Holonomy_origin_eq_winding α hr0 hr1,
    contourU1Holonomy_one_eq_winding α hr0 hr1,
    u1Holonomy_unit_coupling w,
    u1Holonomy_half_origin_ne_one,
    u1Holonomy_half_origin_sq⟩

end InfoGeometry.Canonical.BipolarU1PeriodHolonomy
