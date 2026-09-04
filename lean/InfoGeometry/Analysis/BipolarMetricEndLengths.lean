import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Radial length of the bipolar logarithmic metric ends

On the real slices of the twice-punctured plane, the norm of the logarithmic
differential is represented by the positive scalar speeds

* `1 / (x * (1 - x))` on `0 < x < 1`;
* `1 / (x * (x - 1))` on `1 < x`.

This file identifies those speeds with the actual norm of `dlog01`, proves exact
truncated integral formulas, and determines their limiting behavior. The two
finite punctures have divergent radial length, while the positive real ray from
`2` to infinity has finite limiting length `log 2`.

These are path-length theorems. They do not by themselves assert a global
Hopf--Rinow or geodesic-completeness classification of the full punctured
Riemannian surface.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarMetricEndLengths

open Filter Set MeasureTheory
open scoped Topology Interval

/-- Positive real-axis speed of the logarithmic metric between the punctures. -/
def middleAxisSpeed (x : ℝ) : ℝ :=
  1 / (x * (1 - x))

/-- Positive real-axis speed of the logarithmic metric beyond the second
puncture. -/
def outerAxisSpeed (x : ℝ) : ℝ :=
  1 / (x * (x - 1))

/-- Primitive of the middle-axis speed on `(0,1)`. -/
def middleAxisPrimitive (x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x)

/-- Primitive of the outer-axis speed on `(1,∞)`. -/
def outerAxisPrimitive (x : ℝ) : ℝ :=
  Real.log (x - 1) - Real.log x

/-- A real point strictly between the punctures belongs to the punctured
complex domain. -/
lemma real_between_mem_punctured01
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ punctured01 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact (ne_of_gt hx0) hre
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith

/-- A real point beyond the second puncture belongs to the punctured domain. -/
lemma real_outer_mem_punctured01
    {x : ℝ} (hx : 1 < x) :
    (x : ℂ) ∈ punctured01 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith

/-- The middle-axis scalar speed is exactly the norm of the global logarithmic
differential. -/
theorem norm_dlog01_real_between
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖dlog01 (x : ℂ)‖ = middleAxisSpeed x := by
  have hs := real_between_mem_punctured01 hx0 hx1
  have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [dlog01_eq_one_div_mul hs, norm_div, norm_one, norm_mul,
    Complex.norm_real, hcast, Complex.norm_real,
    Real.norm_of_nonneg hx0.le,
    Real.norm_of_nonneg (sub_nonneg.mpr hx1.le)]
  rfl

/-- The outer-axis scalar speed is exactly the norm of the global logarithmic
differential. -/
theorem norm_dlog01_real_outer
    {x : ℝ} (hx : 1 < x) :
    ‖dlog01 (x : ℂ)‖ = outerAxisSpeed x := by
  have hs := real_outer_mem_punctured01 hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hnorm : ‖(1 - x : ℝ)‖ = x - 1 := by
    rw [Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hx)]
    ring
  rw [dlog01_eq_one_div_mul hs, norm_div, norm_one, norm_mul,
    Complex.norm_real, hcast, Complex.norm_real,
    Real.norm_of_nonneg hx0.le, hnorm]
  rfl

/-- Equal Euclidean distance from `0` and `1` is exactly the vertical
bisector. -/
theorem norm_eq_norm_one_sub_iff_re_eq_half (s : ℂ) :
    ‖s‖ = ‖1 - s‖ ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hsq : Complex.normSq s = Complex.normSq (1 - s) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
    simp [Complex.normSq_apply] at hsq
    nlinarith
  · intro hre
    have hmirror : mirror s = s := (mirror_fixed_iff s).2 hre
    have hc := congrArg Complex.conj hmirror
    have hone : 1 - s = Complex.conj s := by
      simpa [mirror] using hc
    rw [hone, Complex.norm_conj]

/-- Exact critical-line theorem for the logarithmic radial coordinate. -/
theorem eta_zero_iff_re_eq_half
    {s : ℂ} (hs : s ∈ punctured01) :
    eta s = 0 ↔ s.re = 1 / 2 :=
  (eta_eq_zero_iff_equidistant hs).trans
    (norm_eq_norm_one_sub_iff_re_eq_half s)

/-- The middle-axis logarithmic speed is strictly positive. -/
theorem middleAxisSpeed_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < middleAxisSpeed x := by
  unfold middleAxisSpeed
  positivity

/-- The outer-axis logarithmic speed is strictly positive. -/
theorem outerAxisSpeed_pos {x : ℝ} (hx : 1 < x) :
    0 < outerAxisSpeed x := by
  unfold outerAxisSpeed
  positivity

/-- Genuine derivative of the middle-axis primitive. -/
theorem hasDerivAt_middleAxisPrimitive
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt middleAxisPrimitive (middleAxisSpeed x) x := by
  have hlogx : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log (ne_of_gt hx0)
  have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hlogone :
      HasDerivAt (fun t : ℝ => Real.log (1 - t))
        ((1 - x)⁻¹ * (-1)) x :=
    (Real.hasDerivAt_log (ne_of_gt (sub_pos.mpr hx1))).comp x hinner
  have h := hlogx.sub hlogone
  convert h using 1
  · rfl
  · unfold middleAxisSpeed
    field_simp [ne_of_gt hx0, ne_of_gt (sub_pos.mpr hx1)]
    ring

/-- Genuine derivative of the outer-axis primitive. -/
theorem hasDerivAt_outerAxisPrimitive
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt outerAxisPrimitive (outerAxisSpeed x) x := by
  have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hlogsub :
      HasDerivAt (fun t : ℝ => Real.log (t - 1)) (x - 1)⁻¹ x :=
    (Real.hasDerivAt_log (ne_of_gt (sub_pos.mpr hx))).comp x hsub
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log (ne_of_gt hx0)
  have h := hlogsub.sub hlogx
  convert h using 1
  · rfl
  · unfold outerAxisSpeed
    field_simp [ne_of_gt hx0, ne_of_gt (sub_pos.mpr hx)]
    ring

/-- The middle-axis speed is integrable on every compact subinterval of
`(0,1)`. -/
theorem middleAxisSpeed_intervalIntegrable
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable middleAxisSpeed volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb
  have hsub : ContinuousAt (fun y : ℝ => 1 - y) x :=
    continuousAt_const.sub continuousAt_id
  have hden : ContinuousAt (fun y : ℝ => y * (1 - y)) x :=
    continuousAt_id.mul hsub
  have hne : x * (1 - x) ≠ 0 :=
    mul_ne_zero (ne_of_gt hx0) (ne_of_gt (sub_pos.mpr hx1))
  simpa [middleAxisSpeed, one_div] using (hden.inv₀ hne).continuousWithinAt

/-- The outer-axis speed is integrable on every compact interval contained in
`(1,∞)`. -/
theorem outerAxisSpeed_intervalIntegrable
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable outerAxisSpeed volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hsub : ContinuousAt (fun y : ℝ => y - 1) x :=
    continuousAt_id.sub continuousAt_const
  have hden : ContinuousAt (fun y : ℝ => y * (y - 1)) x :=
    continuousAt_id.mul hsub
  have hne : x * (x - 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt hx0) (ne_of_gt (sub_pos.mpr hx1))
  simpa [outerAxisSpeed, one_div] using (hden.inv₀ hne).continuousWithinAt

/-- Exact length integral on a compact subinterval of `(0,1)`. -/
theorem integral_middleAxisSpeed
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ x in a..b, middleAxisSpeed x) =
      middleAxisPrimitive b - middleAxisPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_middleAxisPrimitive
      (lt_of_lt_of_le ha hx.1) (lt_of_le_of_lt hx.2 hb)
  · exact middleAxisSpeed_intervalIntegrable ha hab hb

/-- Exact length integral on a compact interval in `(1,∞)`. -/
theorem integral_outerAxisSpeed
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, outerAxisSpeed x) =
      outerAxisPrimitive b - outerAxisPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_outerAxisPrimitive (lt_of_lt_of_le ha hx.1)
  · exact outerAxisSpeed_intervalIntegrable ha hab

/-- Truncated radial length approaching the puncture at `0`. -/
def originTruncatedLength (ε : ℝ) : ℝ :=
  ∫ x in ε..(1 / 2), middleAxisSpeed x

/-- Truncated radial length approaching the puncture at `1`. -/
def oneTruncatedLength (ε : ℝ) : ℝ :=
  ∫ x in (1 / 2)..(1 - ε), middleAxisSpeed x

/-- Truncated positive-real radial length toward infinity. -/
def infinityTruncatedLength (R : ℝ) : ℝ :=
  ∫ x in 2..R, outerAxisSpeed x

/-- Exact truncated length at the origin end. -/
theorem originTruncatedLength_eq
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε ≤ 1 / 2) :
    originTruncatedLength ε = Real.log (1 - ε) - Real.log ε := by
  rw [originTruncatedLength,
    integral_middleAxisSpeed (a := ε) (b := (1 / 2 : ℝ))
      hε0 hεh (by norm_num)]
  have hhalf : middleAxisPrimitive (1 / 2) = 0 := by
    simp [middleAxisPrimitive]
  rw [hhalf, zero_sub]
  unfold middleAxisPrimitive
  ring

/-- Exact truncated length at the second finite puncture. -/
theorem oneTruncatedLength_eq
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε ≤ 1 / 2) :
    oneTruncatedLength ε = Real.log (1 - ε) - Real.log ε := by
  have hab : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
  have hb : 1 - ε < (1 : ℝ) := by linarith
  rw [oneTruncatedLength,
    integral_middleAxisSpeed (a := (1 / 2 : ℝ)) (b := 1 - ε)
      (by norm_num) hab hb]
  have hhalf : middleAxisPrimitive (1 / 2) = 0 := by
    simp [middleAxisPrimitive]
  rw [hhalf, sub_zero]
  unfold middleAxisPrimitive
  rw [show 1 - (1 - ε) = ε by ring]

/-- The two finite ends have equal truncated radial lengths. -/
theorem originTruncatedLength_eq_oneTruncatedLength
    {ε : ℝ} (hε0 : 0 < ε) (hεh : ε ≤ 1 / 2) :
    originTruncatedLength ε = oneTruncatedLength ε := by
  rw [originTruncatedLength_eq hε0 hεh,
    oneTruncatedLength_eq hε0 hεh]

/-- Exact radial length from `2` to a finite endpoint `R`. -/
theorem infinityTruncatedLength_eq
    {R : ℝ} (hR : 2 ≤ R) :
    infinityTruncatedLength R = outerAxisPrimitive R + Real.log 2 := by
  rw [infinityTruncatedLength,
    integral_outerAxisSpeed (a := (2 : ℝ)) (b := R) (by norm_num) hR]
  have htwo : outerAxisPrimitive 2 = -Real.log 2 := by
    simp [outerAxisPrimitive]
  rw [htwo]
  ring

/-- The common finite-puncture length formula diverges at the right-hand
neighborhood of zero. -/
theorem tendsto_finitePunctureLengthFormula :
    Tendsto (fun ε : ℝ => Real.log (1 - ε) - Real.log ε)
      (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0)
    (Real.log (1 / 2) : ℝ)
  · have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    filter_upwards [Ioc_mem_nhdsGT hhalf] with ε hε
    gcongr
    linarith [hε.2]
  · apply tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero

/-- The puncture at `0` is at infinite radial length along the middle real
axis. -/
theorem tendsto_originTruncatedLength :
    Tendsto originTruncatedLength (𝓝[>] 0) atTop := by
  refine (tendsto_congr' ?_).2 tendsto_finitePunctureLengthFormula
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [Ioc_mem_nhdsGT hhalf] with ε hε
  exact originTruncatedLength_eq hε.1 hε.2

/-- The puncture at `1` is at infinite radial length along the middle real
axis. -/
theorem tendsto_oneTruncatedLength :
    Tendsto oneTruncatedLength (𝓝[>] 0) atTop := by
  refine (tendsto_congr' ?_).2 tendsto_finitePunctureLengthFormula
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [Ioc_mem_nhdsGT hhalf] with ε hε
  exact oneTruncatedLength_eq hε.1 hε.2

/-- The outer-axis primitive tends to zero at infinity. -/
theorem tendsto_outerAxisPrimitive_atTop :
    Tendsto outerAxisPrimitive atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have harg :
      Tendsto (fun x : ℝ => (1 : ℝ) - x⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hlog :
      Tendsto (fun x : ℝ => Real.log (1 - x⁻¹)) atTop (𝓝 0) := by
    have h :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
    simpa using h
  refine (tendsto_congr' ?_).2 hlog
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hx1 : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hratio : (x - 1) / x = 1 - x⁻¹ := by
    field_simp [hx0]
    ring
  calc
    outerAxisPrimitive x = Real.log (x - 1) - Real.log x := rfl
    _ = Real.log ((x - 1) / x) :=
      (Real.log_div hx1 hx0).symm
    _ = Real.log (1 - x⁻¹) := by rw [hratio]

/-- The positive-real end at infinity is reached in finite radial length, with
exact limiting length `log 2` from the base point `2`. -/
theorem tendsto_infinityTruncatedLength :
    Tendsto infinityTruncatedLength atTop (𝓝 (Real.log 2)) := by
  have hbase :
      Tendsto (fun R : ℝ => outerAxisPrimitive R + Real.log 2)
        atTop (𝓝 (Real.log 2)) := by
    simpa using tendsto_outerAxisPrimitive_atTop.add tendsto_const_nhds
  refine (tendsto_congr' ?_).2 hbase
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  exact infinityTruncatedLength_eq hR

/-- Compact radial-end theorem: the two finite punctures are infinitely far
along the middle real axis, whereas positive-real escape to infinity has finite
length. -/
theorem bipolar_metric_end_length_packet :
    Tendsto originTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto oneTruncatedLength (𝓝[>] 0) atTop ∧
      Tendsto infinityTruncatedLength atTop (𝓝 (Real.log 2)) := by
  exact ⟨tendsto_originTruncatedLength,
    tendsto_oneTruncatedLength,
    tendsto_infinityTruncatedLength⟩

end InfoGeometry.Analysis.BipolarMetricEndLengths
