import InfoGeometry.Analysis.BipolarSimplePoleResidues

/-!
# Simple-pole reflection, differential pullback, and non-removability

This extends the existing punctured-limit owner. The predicate certifies a
simple-pole coefficient; meromorphicity is a separate hypothesis if a general
function is to be called meromorphic. No nonexistent global `residue` API is used.

For coefficients, `f (-z)` has residue `-r` at `-a`; the pullback of the
one-form `f(z) dz` is `-f(-z) dz` and has residue `r`. The map `z ↦ -z` is
holomorphic and preserves real orientation. Neither equality removes a pole.
-/

noncomputable section

namespace InfoGeometry.Analysis.SimplePoleReflection

open Filter
open scoped Topology
open InfoGeometry.Analysis.BipolarSimplePoleResidues
open InfoGeometry.Analysis.BipolarLogDifferential

theorem coefficient_unique {f : ℂ → ℂ} {a r s : ℂ}
    (hr : HasSimplePoleCoefficientAt f a r)
    (hs : HasSimplePoleCoefficientAt f a s) : r = s :=
  tendsto_nhds_unique hr hs

theorem coefficient_neg {f : ℂ → ℂ} {a r : ℂ}
    (h : HasSimplePoleCoefficientAt f a r) :
    HasSimplePoleCoefficientAt (fun z => -f z) a (-r) := by
  simpa only [HasSimplePoleCoefficientAt, mul_neg] using h.neg

theorem coefficient_simple_fraction (a r : ℂ) :
    HasSimplePoleCoefficientAt (fun z => r / (z - a)) a r := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  field_simp

theorem neg_tendsto_punctured (a : ℂ) :
    Tendsto (fun z : ℂ => -z) (𝓝[≠] (-a)) (𝓝[≠] a) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using
      (continuousAt_id.neg.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun z : ℂ => -z) (𝓝[≠] (-a)) (𝓝 (-(-a))))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ -a := by simpa using hz
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_iff_eq_neg] using hz'

/-- Reflection of the coefficient alone reverses the simple-pole coefficient. -/
theorem coefficient_reflection {f : ℂ → ℂ} {a r : ℂ}
    (h : HasSimplePoleCoefficientAt f a r) :
    HasSimplePoleCoefficientAt (fun z => f (-z)) (-a) (-r) := by
  have hc := (h.comp (neg_tendsto_punctured a)).neg
  apply hc.congr'
  filter_upwards [] with z
  simp only [Function.comp_apply]
  ring

/-- Including the differential Jacobian gives the same residue, not its negative. -/
theorem coefficient_oneForm_pullback {f : ℂ → ℂ} {a r : ℂ}
    (h : HasSimplePoleCoefficientAt f a r) :
    HasSimplePoleCoefficientAt (fun z => -f (-z)) (-a) r := by
  simpa using coefficient_neg (coefficient_reflection h)

/-- A nonzero coefficient excludes every continuous extension of the punctured germ. -/
theorem nonzero_coefficient_no_continuous_extension
    {f : ℂ → ℂ} {a r : ℂ}
    (h : HasSimplePoleCoefficientAt f a r) (hr : r ≠ 0) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g a ∧ f =ᶠ[𝓝[≠] a] g := by
  rintro ⟨g, hg, hfg⟩
  have hzero : HasSimplePoleCoefficientAt f a 0 := by
    have hc : ContinuousAt (fun z : ℂ => (z - a) * g z) a :=
      (continuousAt_id.sub continuousAt_const).mul hg
    have hc' : Tendsto (fun z => (z - a) * g z) (𝓝[≠] a) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply hc'.congr'
    filter_upwards [hfg] with z hz
    rw [hz]
  exact hr (coefficient_unique h hzero)

/-- The proposed signed-reflection residue theorem fails already for `1/z`. -/
theorem signed_reflection_counterexample :
    HasSimplePoleCoefficientAt (fun z : ℂ => -(1 / (-z))) 0 1 ∧
      ¬ HasSimplePoleCoefficientAt (fun z : ℂ => -(1 / (-z))) 0 (-1) := by
  have h : HasSimplePoleCoefficientAt (fun z : ℂ => -(1 / (-z))) 0 1 := by
    simpa using coefficient_oneForm_pullback (coefficient_simple_fraction 0 1)
  refine ⟨h, fun hn => ?_⟩
  have heq := coefficient_unique h hn
  norm_num at heq

/-- Opposite certified residues coexist with a non-removable local pole. -/
theorem balanced_residues_do_not_imply_removability :
    HasSimplePoleCoefficientAt dlog01 0 1 ∧
    HasSimplePoleCoefficientAt dlog01 1 (-1) ∧
    (1 : ℂ) + (-1) = 0 ∧
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g 0 ∧ dlog01 =ᶠ[𝓝[≠] 0] g := by
  exact ⟨dlog01_hasSimplePoleCoefficientAt_zero,
    dlog01_hasSimplePoleCoefficientAt_one, by ring,
    nonzero_coefficient_no_continuous_extension
      dlog01_hasSimplePoleCoefficientAt_zero one_ne_zero⟩

/-- Infinity-chart coefficient of `(r/z) dz`, including `dz = -dw/w²`. -/
theorem simple_fraction_infinity_chart (r w : ℂ) :
    (-(1 / w ^ 2)) * (r / (1 / w)) = -r / w := by
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- The sphere example has opposite residues at zero and infinity; both persist. -/
theorem simple_fraction_infinity_coefficient (r : ℂ) :
    HasSimplePoleCoefficientAt
      (fun w : ℂ => (-(1 / w ^ 2)) * (r / (1 / w))) 0 (-r) := by
  simpa only [simple_fraction_infinity_chart, sub_zero] using
    coefficient_simple_fraction 0 (-r)

/-- The holomorphic involution has a single fixed point. -/
theorem one_sub_fixed_iff (s : ℂ) : 1 - s = s ↔ s = 1 / 2 := by
  constructor
  · intro h
    linear_combination -h / 2
  · intro h
    rw [h]
    norm_num

/-- The critical line is fixed by the antiholomorphic reflection instead. -/
theorem conjugate_reflection_fixed_iff (s : ℂ) :
    1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  · intro h
    apply Complex.ext
    · change 1 - s.re = s.re
      linarith
    · simp

end InfoGeometry.Analysis.SimplePoleReflection
