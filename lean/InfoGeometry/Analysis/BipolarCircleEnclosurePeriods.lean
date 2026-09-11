import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Circle enclosure periods and the obstruction to a global primitive

This extends the existing elementary-contour owner; it does not replace its
Cauchy--Goursat proof or introduce another logarithmic coefficient.

For a nonnegative radius and a circle avoiding both punctures, the integral
of the repository-owned `dlog01` is the residue pairing of the two disk
membership indicators.  These indicators take values in the existing
`WindingPair` carrier.  Their identification with a general path's topological
winding numbers is not assumed or claimed here.

The nonzero elementary period also rules out a single-valued holomorphic
primitive on the punctured plane.  A negative-radius counterexample records
why a closed-ball exclusion lemma must retain its radius hypothesis.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCircleEnclosurePeriods

open scoped Interval Real
open Complex Metric Set
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarElementaryContourPeriods

/-- Integer indicator of strict disk membership; this is not a new path type. -/
def poleEnclosureIndex (c : ℂ) (r : ℝ) (w : ℂ) : ℤ := by
  classical
  exact if w ∈ ball c r then 1 else 0

/-- The two disk indicators, valued in the existing integer-pair carrier. -/
def circleEnclosurePair (c : ℂ) (r : ℝ) : WindingPair :=
  (poleEnclosureIndex c r 0, poleEnclosureIndex c r 1)

/-- A pole off the circle is integrable; the absolute radius is handled explicitly. -/
theorem circleIntegrable_pole_of_not_mem_sphere
    {c w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : w ∉ sphere c r) :
    CircleIntegrable (fun z : ℂ => (z - w)⁻¹) c r := by
  apply circleIntegrable_sub_inv_iff.mpr
  exact Or.inr (by simpa only [abs_of_nonneg hr] using hw)

/-- Cauchy's formula inside the disk and the existing Cauchy--Goursat theorem
outside it give one exact enclosure formula. -/
theorem circleIntegral_pole_eq_enclosure
    {c w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : w ∉ sphere c r) :
    (∮ z in C(c, r), (z - w)⁻¹) =
      (poleEnclosureIndex c r w : ℂ) * (2 * Real.pi * I) := by
  classical
  by_cases hin : w ∈ ball c r
  · simpa [poleEnclosureIndex, hin] using
      (circleIntegral.integral_sub_inv_of_mem_ball hin)
  · have hout : w ∉ closedBall c r := by
      intro hclosed
      apply hw
      apply mem_sphere.mpr
      exact le_antisymm (mem_closedBall.mp hclosed)
        (not_lt.mp (fun hlt => hin (mem_ball.mpr hlt)))
    simpa [poleEnclosureIndex, hin] using
      (circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hr hout)

/-- Integrability of the full logarithmic differential is proved before
applying linearity of the integral. -/
theorem circleIntegrable_dlog01_of_avoids_punctures
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    CircleIntegrable dlog01 c r := by
  have heq : dlog01 = fun z : ℂ => (z - 0)⁻¹ - (z - 1)⁻¹ := by
    funext z
    rw [dlog01_eq_origin_pole_sub_one_pole]
    ring
  rw [heq]
  simpa only [sub_eq_add_neg] using
    (circleIntegrable_pole_of_not_mem_sphere hr h0).add
      (circleIntegrable_pole_of_not_mem_sphere hr h1).neg

/-- The complete circle integral is the difference of the two enclosed-pole
contributions, with no hypothesis about either integral's value. -/
theorem circleIntegral_dlog01_eq_enclosure_difference
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    (∮ z in C(c, r), dlog01 z) =
      (poleEnclosureIndex c r 0 : ℂ) * (2 * Real.pi * I) -
        (poleEnclosureIndex c r 1 : ℂ) * (2 * Real.pi * I) := by
  calc
    (∮ z in C(c, r), dlog01 z) =
        ∮ z in C(c, r), (z - 0)⁻¹ - (z - 1)⁻¹ := by
          apply circleIntegral.integral_congr hr
          intro z _hz
          rw [dlog01_eq_origin_pole_sub_one_pole]
          ring
    _ = (∮ z in C(c, r), (z - 0)⁻¹) -
        (∮ z in C(c, r), (z - 1)⁻¹) :=
          circleIntegral.integral_sub
            (circleIntegrable_pole_of_not_mem_sphere hr h0)
            (circleIntegrable_pole_of_not_mem_sphere hr h1)
    _ = _ := by
      rw [circleIntegral_pole_eq_enclosure hr h0,
        circleIntegral_pole_eq_enclosure hr h1]

/-- Analytic contour integration lands in the already installed period map. -/
theorem circleIntegral_dlog01_eq_circulationPeriod
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    (∮ z in C(c, r), dlog01 z) =
      circulationPeriod (circleEnclosurePair c r) := by
  rw [circleIntegral_dlog01_eq_enclosure_difference hr h0 h1]
  simp only [circulationPeriod, residueWinding, circleEnclosurePair, Int.cast_sub]
  ring

/-- A circle enclosing both punctures has zero total period, not twice the
one-puncture period. -/
theorem circleIntegral_dlog01_of_both_inside
    {c : ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ball c r) (h1 : (1 : ℂ) ∈ ball c r) :
    (∮ z in C(c, r), dlog01 z) = 0 := by
  have hr : 0 ≤ r := (lt_of_le_of_lt dist_nonneg (mem_ball.mp h0)).le
  have hs0 : (0 : ℂ) ∉ sphere c r := by
    intro hs
    exact (ne_of_lt (mem_ball.mp h0)) (mem_sphere.mp hs)
  have hs1 : (1 : ℂ) ∉ sphere c r := by
    intro hs
    exact (ne_of_lt (mem_ball.mp h1)) (mem_sphere.mp hs)
  rw [circleIntegral_dlog01_eq_enclosure_difference hr hs0 hs1]
  simp [poleEnclosureIndex, h0, h1]

/-- A circle whose closed disk excludes both punctures has zero total period. -/
theorem circleIntegral_dlog01_of_both_outside
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ closedBall c r) (h1 : (1 : ℂ) ∉ closedBall c r) :
    (∮ z in C(c, r), dlog01 z) = 0 := by
  have hs0 : (0 : ℂ) ∉ sphere c r := fun h => h0 (sphere_subset_closedBall h)
  have hs1 : (1 : ℂ) ∉ sphere c r := fun h => h1 (sphere_subset_closedBall h)
  have hb0 : (0 : ℂ) ∉ ball c r := fun h => h0 (ball_subset_closedBall h)
  have hb1 : (1 : ℂ) ∉ ball c r := fun h => h1 (ball_subset_closedBall h)
  rw [circleIntegral_dlog01_eq_enclosure_difference hr hs0 hs1]
  simp [poleEnclosureIndex, hb0, hb1]

/-- Equality of the enclosure pairs is sufficient for equality of circle
periods.  This is not asserted to classify arbitrary loop homotopies. -/
theorem circleIntegral_dlog01_eq_of_enclosurePair_eq
    {c d : ℂ} {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hc0 : (0 : ℂ) ∉ sphere c r) (hc1 : (1 : ℂ) ∉ sphere c r)
    (hd0 : (0 : ℂ) ∉ sphere d t) (hd1 : (1 : ℂ) ∉ sphere d t)
    (hpair : circleEnclosurePair c r = circleEnclosurePair d t) :
    (∮ z in C(c, r), dlog01 z) = (∮ z in C(d, t), dlog01 z) := by
  rw [circleIntegral_dlog01_eq_circulationPeriod hr hc0 hc1,
    circleIntegral_dlog01_eq_circulationPeriod ht hd0 hd1, hpair]

/-- The full exponential character kills every regular circle period. -/
theorem exp_circleIntegral_dlog01
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h0 : (0 : ℂ) ∉ sphere c r) (h1 : (1 : ℂ) ∉ sphere c r) :
    Complex.exp (∮ z in C(c, r), dlog01 z) = 1 := by
  rw [circleIntegral_dlog01_eq_circulationPeriod hr h0 h1]
  exact exp_circulationPeriod _

/-- The elementary origin circle is contained in the punctured domain. -/
theorem sphere_origin_subset_punctured01
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    sphere (0 : ℂ) r ⊆ punctured01 := by
  intro z hz
  constructor
  · intro heq
    subst z
    have hzero : (0 : ℝ) = r := by simpa using (mem_sphere.mp hz)
    exact hr0.ne' hzero.symm
  · intro heq
    subst z
    have hone : (1 : ℝ) = r := by simpa using (mem_sphere.mp hz)
    exact hr1.ne hone.symm

/-- Even a single-valued primitive with the indicated derivative along the
entire elementary circle is impossible. -/
theorem no_primitive_on_origin_circle
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ ∃ F : ℂ → ℂ, ∀ z ∈ sphere (0 : ℂ) r,
      HasDerivWithinAt F (dlog01 z) (sphere (0 : ℂ) r) z := by
  rintro ⟨F, hF⟩
  have hzero : (∮ z in C(0, r), dlog01 z) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr0.le hF
  rw [circleIntegral_dlog01_origin hr0 hr1] at hzero
  exact Complex.two_pi_I_ne_zero hzero

/-- The global logarithmic differential is not the derivative of a
single-valued holomorphic potential on the twice-punctured plane. -/
theorem no_global_dlog01_primitive :
    ¬ ∃ F : ℂ → ℂ, ∀ z ∈ punctured01, HasDerivAt F (dlog01 z) z := by
  rintro ⟨F, hF⟩
  apply no_primitive_on_origin_circle (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨F, ?_⟩
  intro z hz
  exact (hF z (sphere_origin_subset_punctured01
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hz)).hasDerivWithinAt

/-- Regression witness against dropping `0 ≤ r` from the exterior-pole
lemma: a negative-radius closed ball is empty, but the circle integral is not. -/
theorem negative_radius_exterior_counterexample :
    (0 : ℂ) ∉ closedBall (0 : ℂ) (-1 : ℝ) ∧
      (∮ z in C((0 : ℂ), (-1 : ℝ)), (z - 0)⁻¹) =
        (2 * Real.pi * I : ℂ) := by
  constructor
  · simp [mem_closedBall]
  · exact circleIntegral.integral_sub_center_inv 0 (by norm_num)

end InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
