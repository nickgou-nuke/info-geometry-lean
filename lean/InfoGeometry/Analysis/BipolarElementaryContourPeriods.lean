import InfoGeometry.Analysis.BipolarPeriodDescent
import InfoGeometry.Analysis.BipolarWindingExactSequence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Elementary contour periods of the bipolar logarithmic differential

The algebraic winding owner records the residue-difference period map

`(m,n) ↦ (m-n) 2πi`.

This file closes the nearest analytic edge: it integrates the full differential

`dlog01(z) = 1/z - 1/(z-1)`

on positively oriented circles of radius `r` with `0 < r < 1` around the two
punctures.  The singular summand is evaluated by Mathlib's native circle
integral, while the other summand is killed by the native Cauchy--Goursat
theorem because its pole lies outside the closed disk.

The resulting integrals are identified with `circulationPeriod originWinding`
and `circulationPeriod oneWinding`.  No classification of arbitrary loops or
identification of singular homology is asserted.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarElementaryContourPeriods

open scoped Interval Real
open Complex Metric Set
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarWindingExactSequence

/-- Exact decomposition of the bipolar logarithmic coefficient into its two
simple-pole summands. -/
theorem dlog01_eq_origin_pole_sub_one_pole (z : ℂ) :
    dlog01 z = (z - 0)⁻¹ + (-1 : ℂ) * (z - 1)⁻¹ := by
  rw [dlog01]
  simp only [one_div, sub_zero]
  rw [show (1 : ℂ) - z = -(z - 1) by ring, inv_neg]
  ring

/-- A Cauchy kernel whose pole is outside the closed disk has zero circle
integral.  This is the regular-part lemma needed for the two elementary bipolar
contours. -/
theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {c w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) :
    (∮ z in C(c, r), (z - w)⁻¹) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr Set.countable_empty ?_ ?_
  · exact (continuousOn_id.sub continuousOn_const).inv₀ (by
      intro z hz hzero
      apply hw
      have hzw : z = w := sub_eq_zero.mp hzero
      simpa [hzw] using hz)
  · intro z hz
    have hzw : z - w ≠ 0 := by
      intro hzero
      apply hw
      have heq : z = w := sub_eq_zero.mp hzero
      have hzclosed : z ∈ closedBall c r := ball_subset_closedBall hz.1
      simpa [heq] using hzclosed
    simpa using (((hasDerivAt_id z).sub_const w).inv hzw).differentiableAt

/-- A centered Cauchy pole is circle-integrable whenever the radius is positive. -/
theorem circleIntegrable_centerPole
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    CircleIntegrable (fun z : ℂ => (z - c)⁻¹) c r := by
  rw [circleIntegrable_sub_inv_iff]
  refine Or.inr ?_
  rw [abs_of_pos hr]
  intro hmem
  have hzero : (0 : ℝ) = r := by
    simpa using (mem_sphere.mp hmem)
  exact (ne_of_gt hr) hzero.symm

/-- A Cauchy pole outside the closed disk is circle-integrable. -/
theorem circleIntegrable_sub_inv_of_not_mem_closedBall
    {c w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) :
    CircleIntegrable (fun z : ℂ => (z - w)⁻¹) c r := by
  rw [circleIntegrable_sub_inv_iff]
  refine Or.inr ?_
  rw [abs_of_nonneg hr]
  intro hmem
  exact hw (sphere_subset_closedBall hmem)

lemma one_not_mem_closedBall_zero
    {r : ℝ} (hr : r < 1) :
    (1 : ℂ) ∉ closedBall 0 r := by
  intro hmem
  have hle : dist (1 : ℂ) 0 ≤ r := mem_closedBall.mp hmem
  have hdist : dist (1 : ℂ) 0 = 1 := by
    simp
  rw [hdist] at hle
  exact (not_le_of_gt hr) hle

lemma zero_not_mem_closedBall_one
    {r : ℝ} (hr : r < 1) :
    (0 : ℂ) ∉ closedBall 1 r := by
  intro hmem
  have hle : dist (0 : ℂ) 1 ≤ r := mem_closedBall.mp hmem
  have hdist : dist (0 : ℂ) 1 = 1 := by
    simp
  rw [hdist] at hle
  exact (not_le_of_gt hr) hle

/-- The full bipolar logarithmic differential has period `+2πi` on a small
positive circle around the origin. -/
theorem circleIntegral_dlog01_origin
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C(0, r), dlog01 z) =
      (2 * Real.pi * Complex.I : ℂ) := by
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
  have hregularIntegral :
      (∮ z in C(0, r), (z - 1)⁻¹) = 0 :=
    circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hr0.le
      (one_not_mem_closedBall_zero hr1)
  calc
    (∮ z in C(0, r), dlog01 z) =
        ∮ z in C(0, r), (z - 0)⁻¹ + (-1 : ℂ) * (z - 1)⁻¹ := by
          exact circleIntegral.integral_congr hr0.le
            (fun z _hz => dlog01_eq_origin_pole_sub_one_pole z)
    _ = (∮ z in C(0, r), (z - 0)⁻¹) +
        ∮ z in C(0, r), (-1 : ℂ) * (z - 1)⁻¹ := by
          exact circleIntegral.integral_add hpole hregular
    _ = (2 * Real.pi * Complex.I : ℂ) + (-1 : ℂ) * 0 := by
          rw [circleIntegral.integral_sub_center_inv 0 hr0.ne',
            circleIntegral.integral_const_mul, hregularIntegral]
    _ = (2 * Real.pi * Complex.I : ℂ) := by ring

/-- The full bipolar logarithmic differential has period `-2πi` on a small
positive circle around the second puncture. -/
theorem circleIntegral_dlog01_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C((1 : ℂ), r), dlog01 z) =
      -(2 * Real.pi * Complex.I : ℂ) := by
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
  have hregularIntegral :
      (∮ z in C((1 : ℂ), r), (z - 0)⁻¹) = 0 :=
    circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hr0.le
      (zero_not_mem_closedBall_one hr1)
  calc
    (∮ z in C((1 : ℂ), r), dlog01 z) =
        ∮ z in C((1 : ℂ), r),
          (z - 0)⁻¹ + (-1 : ℂ) * (z - 1)⁻¹ := by
            exact circleIntegral.integral_congr hr0.le
              (fun z _hz => dlog01_eq_origin_pole_sub_one_pole z)
    _ = (∮ z in C((1 : ℂ), r), (z - 0)⁻¹) +
        ∮ z in C((1 : ℂ), r), (-1 : ℂ) * (z - 1)⁻¹ := by
          exact circleIntegral.integral_add hregular hpole
    _ = 0 + (-1 : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
          rw [hregularIntegral, circleIntegral.integral_const_mul,
            circleIntegral.integral_sub_center_inv (1 : ℂ) hr0.ne']
    _ = -(2 * Real.pi * Complex.I : ℂ) := by ring

/-- The analytic origin-circle period agrees with the first algebraic winding
generator. -/
theorem circleIntegral_dlog01_origin_eq_circulationPeriod
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C(0, r), dlog01 z) =
      circulationPeriod originWinding := by
  rw [circleIntegral_dlog01_origin hr0 hr1, circulationPeriod_origin]

/-- The analytic second-puncture period agrees with the second algebraic winding
generator. -/
theorem circleIntegral_dlog01_one_eq_circulationPeriod
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C((1 : ℂ), r), dlog01 z) =
      circulationPeriod oneWinding := by
  rw [circleIntegral_dlog01_one hr0 hr1, circulationPeriod_one]

/-- The two elementary periods balance, as dictated by the residue vector
`(+1,-1)`. -/
theorem elementary_circle_periods_balance
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C(0, r), dlog01 z) +
        (∮ z in C((1 : ℂ), r), dlog01 z) = 0 := by
  rw [circleIntegral_dlog01_origin hr0 hr1,
    circleIntegral_dlog01_one hr0 hr1]
  ring

/-- Compact analytic-to-algebraic elementary-period packet. -/
theorem bipolar_elementary_contour_period_packet
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C(0, r), dlog01 z) = circulationPeriod originWinding ∧
      (∮ z in C((1 : ℂ), r), dlog01 z) = circulationPeriod oneWinding := by
  exact ⟨circleIntegral_dlog01_origin_eq_circulationPeriod hr0 hr1,
    circleIntegral_dlog01_one_eq_circulationPeriod hr0 hr1⟩

/-- Additive extension of the two actual circle integrals to integer chains.
This does not identify arbitrary loops with winding pairs. -/
def elementaryContourPeriodHom (r : ℝ) : WindingPair →+ ℂ where
  toFun w := w.1 • (∮ z in C(0, r), dlog01 z) +
    w.2 • (∮ z in C((1 : ℂ), r), dlog01 z)
  map_zero' := by simp
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

/-- The analytic generator pairing recovers the installed residue-period map. -/
theorem elementaryContourPeriodHom_eq_circulationPeriodHom
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    elementaryContourPeriodHom r =
      BipolarWindingExactSequence.circulationPeriodHom := by
  ext w
  change w.1 • (∮ z in C(0, r), dlog01 z) +
    w.2 • (∮ z in C((1 : ℂ), r), dlog01 z) = circulationPeriod w
  rw [circleIntegral_dlog01_origin hr0 hr1, circleIntegral_dlog01_one hr0 hr1]
  simp only [zsmul_eq_mul, circulationPeriod, residueWinding, Int.cast_sub]
  ring

/-- Exactly the diagonal integer chains have vanishing contour pairing. -/
theorem elementaryContourPeriodHom_ker
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (elementaryContourPeriodHom r).ker =
      diagonalWindingSubgroup := by
  rw [elementaryContourPeriodHom_eq_circulationPeriodHom hr0 hr1,
    BipolarWindingExactSequence.circulationPeriodHom_ker]

/-- The actual elementary contour pairing has image `2πiℤ`. -/
theorem elementaryContourPeriodHom_range
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (elementaryContourPeriodHom r).range =
      AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ) := by
  rw [elementaryContourPeriodHom_eq_circulationPeriodHom hr0 hr1,
    BipolarWindingExactSequence.circulationPeriodHom_range_eq_zmultiples]

end InfoGeometry.Analysis.BipolarElementaryContourPeriods
