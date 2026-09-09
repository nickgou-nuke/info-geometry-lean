import InfoGeometry.Analysis.BipolarMetricEndLengths
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Tactic

/-!
# Pullback metric and the missing outer-end completion edge

The outer real ray is equipped with the metric pulled back from the logarithmic
coordinate `outerAxisPrimitive`.  The escape sequence `n ↦ n + 2` is Cauchy
for this metric because its logarithmic coordinates converge to zero.  Zero is
not represented by any point on the outer ray, so the ray is not complete.

This is a one-dimensional completion statement.  It does not assert a global
Riemannian completion theorem for the full punctured complex plane.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarMetricCompletion

open Filter Set
open scoped Topology
open InfoGeometry.Analysis.BipolarMetricEndLengths

/-- The positive real outer ray, with its puncture at `1` removed. -/
def OuterAxis := {x : ℝ // 1 < x}

/-- Logarithmic coordinate of the outer ray. -/
def outerCoordinate (x : OuterAxis) : ℝ :=
  outerAxisPrimitive x.1

theorem outerCoordinate_injective : Function.Injective outerCoordinate := by
  intro x y hxy
  apply Subtype.ext
  change outerAxisPrimitive x.1 = outerAxisPrimitive y.1 at hxy
  have hx0 : 0 < x.1 := lt_trans zero_lt_one x.property
  have hy0 : 0 < y.1 := lt_trans zero_lt_one y.property
  have hx1 : 0 < x.1 - 1 := sub_pos.mpr x.property
  have hy1 : 0 < y.1 - 1 := sub_pos.mpr y.property
  have hexp := congrArg Real.exp hxy
  rw [outerAxisPrimitive, outerAxisPrimitive,
    Real.exp_sub, Real.exp_sub, Real.exp_log hx1, Real.exp_log hx0,
    Real.exp_log hy1, Real.exp_log hy0] at hexp
  field_simp at hexp
  linarith

/-- The pullback of the Euclidean metric along the logarithmic coordinate. -/
noncomputable instance outerAxisMetricSpace : MetricSpace OuterAxis :=
  MetricSpace.induced outerCoordinate outerCoordinate_injective inferInstance

@[simp] theorem dist_outerAxis (x y : OuterAxis) :
    dist x y = dist (outerCoordinate x) (outerCoordinate y) := rfl

theorem outerCoordinate_isometry : Isometry outerCoordinate := by
  intro x y
  rfl

theorem dist_outerAxis_eq_abs_coordinate_sub (x y : OuterAxis) :
    dist x y = |outerCoordinate x - outerCoordinate y| := by
  rw [dist_outerAxis, Real.dist_eq]

/-- The coordinate tends to zero along escape to infinity. -/
def outerEscapeSequence (n : ℕ) : OuterAxis :=
  ⟨(n : ℝ) + 2, by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith⟩

theorem outerEscapeSequence_coordinate_tendsto :
    Tendsto (fun n => outerCoordinate (outerEscapeSequence n)) atTop (𝓝 0) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    have hn : ∀ᶠ n : ℕ in atTop, b - 2 ≤ (n : ℝ) :=
      Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop (b - 2)
    filter_upwards [hn] with n hbn
    linarith
  exact tendsto_outerAxisPrimitive_atTop.comp htop

theorem outerAxisPrimitive_neg (x : OuterAxis) :
    outerCoordinate x < 0 := by
  unfold outerCoordinate outerAxisPrimitive
  have hx0 : 0 < x.1 := lt_trans zero_lt_one x.property
  have hratio : 0 < (x.1 - 1) / x.1 :=
    div_pos (sub_pos.mpr x.property) hx0
  have hratio_lt : (x.1 - 1) / x.1 < 1 := by
    apply (div_lt_iff₀ hx0).2
    linarith
  rw [← Real.log_div (sub_ne_zero.mpr x.property.ne') hx0.ne']
  exact Real.log_neg hratio hratio_lt

/-! The coordinate does not merely embed the outer ray into the negative real
axis: it has an explicit inverse there.  This is the canonical finite
completion readout for the one-dimensional end. -/

noncomputable def outerCoordinateInv (y : {y : ℝ // y < 0}) : OuterAxis :=
  ⟨1 / (1 - Real.exp y), by
    have hy : Real.exp y < 1 := (Real.exp_lt_one_iff).2 y.property
    have hden : 0 < 1 - Real.exp y := sub_pos.mpr hy
    apply (lt_div_iff₀ hden).2
    have hpos : 0 < Real.exp y := Real.exp_pos y
    linarith⟩

theorem outerCoordinate_outerCoordinateInv (y : {y : ℝ // y < 0}) :
    outerCoordinate (outerCoordinateInv y) = y := by
  have hyexp : 0 < Real.exp y := Real.exp_pos y
  have hylt : Real.exp y < 1 := (Real.exp_lt_one_iff).2 y.property
  have hden : 0 < 1 - Real.exp y := sub_pos.mpr hylt
  have hden_ne : 1 - Real.exp y ≠ 0 := ne_of_gt hden
  have hx : (0 : ℝ) < 1 / (1 - Real.exp y) :=
    one_div_pos.mpr hden
  have hxsub : 0 < 1 / (1 - Real.exp y) - 1 := by
    have hlt : 1 - Real.exp y < 1 := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ hden).2 (by linarith))
  unfold outerCoordinate outerCoordinateInv outerAxisPrimitive
  change Real.log (1 / (1 - Real.exp (y : ℝ)) - 1) -
      Real.log (1 / (1 - Real.exp (y : ℝ))) = y
  rw [← Real.log_div (ne_of_gt hxsub) (ne_of_gt hx)]
  have hratio :
      (1 / (1 - Real.exp (y : ℝ)) - 1) /
          (1 / (1 - Real.exp (y : ℝ))) = Real.exp (y : ℝ) := by
    field_simp [hden_ne, Real.exp_ne_zero]
    ring
  rw [hratio, Real.log_exp]

theorem outerCoordinate_range :
    Set.range outerCoordinate = Set.Iio 0 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact outerAxisPrimitive_neg x
  · intro hy
    exact ⟨outerCoordinateInv ⟨y, hy⟩,
      outerCoordinate_outerCoordinateInv ⟨y, hy⟩⟩

/-- The logarithmic coordinate is an equivalence onto the negative half-line.
This is the precise one-dimensional model of the outer metric end. -/
noncomputable def outerCoordinateEquiv : OuterAxis ≃ {y : ℝ // y < 0} where
  toFun x := ⟨outerCoordinate x, outerAxisPrimitive_neg x⟩
  invFun := outerCoordinateInv
  left_inv x := by
    apply outerCoordinate_injective
    exact outerCoordinate_outerCoordinateInv
      ⟨outerCoordinate x, outerAxisPrimitive_neg x⟩
  right_inv y := by
    apply Subtype.ext
    exact outerCoordinate_outerCoordinateInv y

theorem outerCoordinateEquiv_isometry :
    Isometry outerCoordinateEquiv := by
  intro x y
  rfl

theorem outerCoordinateEquiv_cauchy_iff (u : ℕ → OuterAxis) :
    CauchySeq u ↔ CauchySeq (outerCoordinateEquiv ∘ u) := by
  rw [Metric.cauchySeq_iff, Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    exact hN m hm n hn
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    exact hN m hm n hn

theorem outerEscapeSequence_cauchy : CauchySeq outerEscapeSequence := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hcoord := outerEscapeSequence_coordinate_tendsto
  have hsmall : ∀ᶠ n : ℕ in atTop,
      dist (outerCoordinate (outerEscapeSequence n)) 0 < ε / 2 := by
    exact eventually_atTop.2
      (Metric.tendsto_atTop.1 hcoord (ε / 2) (half_pos hε))
  rcases eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_outerAxis]
  calc
    dist (outerCoordinate (outerEscapeSequence m))
        (outerCoordinate (outerEscapeSequence n)) ≤
        dist (outerCoordinate (outerEscapeSequence m)) 0 +
          dist 0 (outerCoordinate (outerEscapeSequence n)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      gcongr
      · exact hN m hm
      · simpa [dist_comm] using hN n hn
    _ = ε := by ring

theorem outerEscapeSequence_no_limit :
    ¬ ∃ x : OuterAxis,
        Tendsto outerEscapeSequence atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have hcoord : Tendsto (fun n => outerCoordinate (outerEscapeSequence n))
      atTop (𝓝 (outerCoordinate x)) := by
    have hi : Isometry outerCoordinate :=
      MetricSpace.isometry_induced outerCoordinate outerCoordinate_injective
    have htransport :=
      (hi.tendsto_nhds_iff
        (g := outerEscapeSequence) (a := atTop) (b := x)).mp hx
    simpa [Function.comp_def] using htransport
  have hzero := outerEscapeSequence_coordinate_tendsto
  have heq : outerCoordinate x = 0 := tendsto_nhds_unique hcoord hzero
  linarith [outerAxisPrimitive_neg x]

theorem outerAxis_not_complete : ¬ CompleteSpace OuterAxis := by
  intro hcomplete
  letI : CompleteSpace OuterAxis := hcomplete
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete outerEscapeSequence_cauchy
  exact outerEscapeSequence_no_limit ⟨x, hx⟩

/-! ## The canonical missing endpoint in the metric completion

The preceding theorem only states incompleteness.  The completion API gives a
more precise readout: the escaping Cauchy sequence converges in the completion,
and its limit is not the image of an outer-axis point.  This remains a
one-dimensional statement; no global completion of the punctured plane is
being inferred from it.
-/

noncomputable def outerEscapeCompletionLimit :
    UniformSpace.Completion OuterAxis :=
  letI : Inhabited OuterAxis := ⟨⟨2, by norm_num⟩⟩
  limUnder atTop
    (fun n => (outerEscapeSequence n : UniformSpace.Completion OuterAxis))

theorem outerEscapeSequence_completion_cauchy :
    CauchySeq
      (fun n => (outerEscapeSequence n : UniformSpace.Completion OuterAxis)) := by
  change Cauchy
    (atTop.map
      (fun n => (outerEscapeSequence n : UniformSpace.Completion OuterAxis)))
  simpa only [Filter.map_map] using
    (Cauchy.map outerEscapeSequence_cauchy
      (UniformSpace.Completion.uniformContinuous_coe (α := OuterAxis)))

theorem outerEscapeSequence_tendsto_completion :
    Tendsto
      (fun n => (outerEscapeSequence n : UniformSpace.Completion OuterAxis))
      atTop (𝓝 outerEscapeCompletionLimit) := by
  simpa only [outerEscapeCompletionLimit] using
    (outerEscapeSequence_completion_cauchy).tendsto_limUnder

theorem outerEscapeCompletionLimit_not_coe (x : OuterAxis) :
    outerEscapeCompletionLimit ≠ (x : UniformSpace.Completion OuterAxis) := by
  intro hlim
  have hcompletion :
      Tendsto
        (fun n => (outerEscapeSequence n : UniformSpace.Completion OuterAxis))
        atTop (𝓝 (x : UniformSpace.Completion OuterAxis)) := by
    simpa [hlim] using outerEscapeSequence_tendsto_completion
  have houter : Tendsto outerEscapeSequence atTop (𝓝 x) := by
    have htransport :=
      (UniformSpace.Completion.coe_isometry.tendsto_nhds_iff
        (g := outerEscapeSequence) (a := atTop) (b := x)).mpr hcompletion
    simpa [Function.comp_def] using htransport
  exact outerEscapeSequence_no_limit ⟨x, houter⟩

end InfoGeometry.Analysis.BipolarMetricCompletion
