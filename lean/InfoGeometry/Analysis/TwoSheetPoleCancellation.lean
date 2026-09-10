import InfoGeometry.Analysis.BipolarSimplePoleResidues

/-!
# Transport and cancellation of actual simple-pole coefficients

The owner predicate is a punctured-neighbourhood limit, not an assigned
residue label.  It also permits coefficient zero and does not itself assert
meromorphicity.  Reflection of a coefficient reverses its pole coefficient;
the Jacobian in the pullback of a one-form reverses that sign again.

Cancellation concerns the signed readout.  A nonzero coefficient still
precludes a continuous extension of either individual channel.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarSimplePoleResidues

open Filter
open scoped Topology

namespace HasSimplePoleCoefficientAt

variable {f g : ℂ → ℂ} {a r s : ℂ}

/-- A punctured-limit coefficient is unique. -/
theorem unique (h : HasSimplePoleCoefficientAt f a r)
    (h' : HasSimplePoleCoefficientAt f a s) : r = s :=
  tendsto_nhds_unique h h'

theorem neg (h : HasSimplePoleCoefficientAt f a r) :
    HasSimplePoleCoefficientAt (fun z => -f z) a (-r) := by
  simpa [HasSimplePoleCoefficientAt] using Filter.Tendsto.neg h

theorem add (hf : HasSimplePoleCoefficientAt f a r)
    (hg : HasSimplePoleCoefficientAt g a s) :
    HasSimplePoleCoefficientAt (fun z => f z + g z) a (r + s) := by
  simpa [HasSimplePoleCoefficientAt, mul_add] using Filter.Tendsto.add hf hg

/-- Reflection of the scalar coefficient contributes one minus sign. -/
theorem reflection (h : HasSimplePoleCoefficientAt f a r) (c : ℂ) :
    HasSimplePoleCoefficientAt (fun z => f (c - z)) (c - a) (-r) := by
  have ht : Tendsto (fun z : ℂ => c - z)
      (𝓝[≠] (c - a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht := ((continuousAt_const :
        ContinuousAt (fun _ : ℂ => c) (c - a)).sub continuousAt_id).tendsto
      simpa using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro he
      apply hz
      linear_combination -he
  have hh := (Filter.Tendsto.neg (h.comp ht))
  change Tendsto (fun z => (z - (c - a)) * f (c - z)) _ _
  convert hh using 1
  funext z
  simp only [Function.comp_apply]
  ring

/-- Pullback of `f(z) dz` includes `d(c-z) = -dz` and preserves residues. -/
theorem reflection_pullback (h : HasSimplePoleCoefficientAt f a r) (c : ℂ) :
    HasSimplePoleCoefficientAt (fun z => -f (c - z)) (c - a) r := by
  simpa using (h.reflection c).neg

/-- Conjugating both the coordinate and coefficient conjugates the residue. -/
theorem conjugate (h : HasSimplePoleCoefficientAt f a r) :
    HasSimplePoleCoefficientAt
      (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) a) ((starRingEnd ℂ) r) := by
  have ht : Tendsto (starRingEnd ℂ)
      (𝓝[≠] ((starRingEnd ℂ) a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc := Complex.continuous_conj.tendsto ((starRingEnd ℂ) a)
      simpa using hc.mono_left
        (y := 𝓝[≠] ((starRingEnd ℂ) a)) nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro he
      apply hz
      simpa using congrArg (starRingEnd ℂ) he
  have hh := Complex.continuous_conj.continuousAt.tendsto.comp (h.comp ht)
  simpa [HasSimplePoleCoefficientAt, Function.comp_def, map_mul, map_sub] using hh

/-- Anti-linear reflection produces the negative conjugate coefficient. -/
theorem conjugate_reflection (h : HasSimplePoleCoefficientAt f a r) (c : ℂ) :
    HasSimplePoleCoefficientAt
      (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) (c - z))))
      (c - (starRingEnd ℂ) a) (-((starRingEnd ℂ) r)) :=
  h.conjugate.reflection c

/-- A finite limit of the unregularized function forces coefficient zero. -/
theorem eq_zero_of_tendsto (h : HasSimplePoleCoefficientAt f a r)
    {b : ℂ} (hf : Tendsto f (𝓝[≠] a) (𝓝 b)) : r = 0 := by
  have ht : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 0) := by
    simpa using ((continuousAt_id : ContinuousAt (fun z : ℂ => z) a).sub
      (continuousAt_const : ContinuousAt (fun _ : ℂ => a) a)).tendsto.mono_left
      (y := 𝓝[≠] a) nhdsWithin_le_nhds
  exact h.unique (by simpa [HasSimplePoleCoefficientAt] using ht.mul hf)

/-- A nonzero simple-pole coefficient has no continuous extension, even if
the value assigned at the puncture is changed. -/
theorem no_continuous_extension (h : HasSimplePoleCoefficientAt f a r)
    (hr : r ≠ 0) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g a ∧ g =ᶠ[𝓝[≠] a] f := by
  rintro ⟨g, hg, he⟩
  exact hr (h.eq_zero_of_tendsto
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' he))

/-- A pure principal part has the indicated punctured-limit coefficient. -/
theorem principal_part (a r : ℂ) :
    HasSimplePoleCoefficientAt (fun z => r / (z - a)) a r := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  simp [hza, div_eq_mul_inv, mul_left_comm]

end HasSimplePoleCoefficientAt

/-- In a common local coordinate, opposite complete principal parts leave
an analytic sum.  The analytic remainders are essential hypotheses. -/
theorem analytic_extension_of_opposite_principal_parts
    {uL uR vL vR : ℂ → ℂ} {a r : ℂ}
    (hL : uL =ᶠ[𝓝[≠] a] fun z => r / (z - a) + vL z)
    (hR : uR =ᶠ[𝓝[≠] a] fun z => -r / (z - a) + vR z)
    (hvL : AnalyticAt ℂ vL a) (hvR : AnalyticAt ℂ vR a) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v a ∧
      v =ᶠ[𝓝[≠] a] (fun z => uL z + uR z) := by
  refine ⟨fun z => vL z + vR z, hvL.add hvR, ?_⟩
  filter_upwards [hL, hR] with z hzL hzR
  rw [hzL, hzR, neg_div]
  ring

/-- The scalar seam law giving opposite coefficients has no extra minus.
For `c = 0`, this is `uR z = uL (-z)`. -/
theorem twin_pole_cancellation {uL uR : ℂ → ℂ} {a c rL rR : ℂ}
    (hL : HasSimplePoleCoefficientAt uL a rL)
    (hR : HasSimplePoleCoefficientAt uR (c - a) rR)
    (hseam : ∀ z, uR z = uL (c - z)) :
    rL + rR = 0 := by
  have heq : uR = fun z => uL (c - z) := funext hseam
  rw [heq] at hR
  have hr : rR = -rL := hR.unique (hL.reflection c)
  simp [hr]

/-- The additional coefficient minus in the proposed seam gives equal
residues.  This includes the Jacobian sign of a one-form pullback. -/
theorem pullback_pole_coefficients_equal {uL uR : ℂ → ℂ} {a c rL rR : ℂ}
    (hL : HasSimplePoleCoefficientAt uL a rL)
    (hR : HasSimplePoleCoefficientAt uR (c - a) rR)
    (hseam : ∀ z, uR z = -uL (c - z)) :
    rR = rL := by
  have heq : uR = fun z => -uL (c - z) := funext hseam
  rw [heq] at hR
  exact hR.unique (hL.reflection_pullback c)

/-- The existing balanced bipolar form retains a singularity at each pole. -/
theorem bipolar_balanced_but_no_continuous_extensions :
    (¬ ∃ g : ℂ → ℂ, ContinuousAt g 0 ∧
      g =ᶠ[𝓝[≠] 0] InfoGeometry.Analysis.BipolarLogDifferential.dlog01) ∧
    (¬ ∃ g : ℂ → ℂ, ContinuousAt g 1 ∧
      g =ᶠ[𝓝[≠] 1] InfoGeometry.Analysis.BipolarLogDifferential.dlog01) := by
  exact ⟨dlog01_hasSimplePoleCoefficientAt_zero.no_continuous_extension one_ne_zero,
    dlog01_hasSimplePoleCoefficientAt_one.no_continuous_extension (neg_ne_zero.mpr one_ne_zero)⟩

end InfoGeometry.Analysis.BipolarSimplePoleResidues
