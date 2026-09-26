import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Enstrophy divergence with spatial hypotheses

The nonnegative Lebesgue integral takes values in `ℝ≥0∞`; unlike the Bochner
integral it records a divergent enstrophy by `∞`. A weak-value pole alone is
not a hypothesis of any divergence theorem here. The spatial input is an
actual vorticity component, or a lower bound for its square.

The power-law result concerns a boundary singularity on an open interval.
The temporal result concerns a spatially uniform vorticity on a region of
unit measure. Neither supplies Navier--Stokes dynamics or regular forcing.
-/

noncomputable section

namespace InfoGeometry.Canonical.EnstrophyDivergence

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The exact local integrability threshold for a nonnegative power density. -/
theorem rpow_lintegral_ne_top_iff {s a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal (x ^ s)) ≠ ∞ ↔ -1 < s := by
  have hc : ContinuousOn (fun x : ℝ => x ^ s) (Ioo 0 a) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) a)] (fun x => x ^ s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg hx.1.le s
  exact (lintegral_ofReal_ne_top_iff_integrable
    (hc.aestronglyMeasurable measurableSet_Ioo) hn).trans
      (intervalIntegral.integrableOn_Ioo_rpow_iff ha)

/-- Endpoint exponent `-1` is included in the divergent regime. -/
theorem rpow_lintegral_eq_top_iff {s a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal (x ^ s)) = ∞ ↔ s ≤ -1 := by
  constructor
  · intro h
    by_contra hs
    exact ((rpow_lintegral_ne_top_iff ha).2 (by linarith)) h
  · intro hs
    by_contra h
    have := (rpow_lintegral_ne_top_iff ha).1 h
    linarith

/-- A square-vorticity lower bound transfers a genuine divergent spatial
integral; an upper estimate for a gradient would not imply this conclusion. -/
theorem enstrophy_eq_top_of_rpow_lower_bound {omega : ℝ → ℝ} {s a : ℝ}
    (ha : 0 < a) (hs : s ≤ -1)
    (hbound : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) a), x ^ s ≤ omega x ^ 2) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal (omega x ^ 2)) = ∞ := by
  apply top_unique
  rw [← (rpow_lintegral_eq_top_iff ha).2 hs]
  exact lintegral_mono_ae (hbound.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))

/-- The derivative of the reciprocal shear is `-1 / x²`; its squared
vorticity has nonintegrable density `x⁻⁴` near the excluded boundary. -/
theorem reciprocal_shear_enstrophy_eq_top {a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((-(x ^ 2)⁻¹) ^ 2)) = ∞ := by
  have heq (x : ℝ) (hx : 0 ≤ x) : (-(x ^ 2)⁻¹) ^ 2 = x ^ (-4 : ℝ) := by
    change (-(x ^ 2)⁻¹) ^ 2 = x ^ (-(4 : ℕ) : ℝ)
    rw [Real.rpow_neg hx, Real.rpow_natCast]
    simp [inv_pow, ← pow_mul]
  calc
    _ = ∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal (x ^ (-4 : ℝ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [heq x hx.1.le]
    _ = ∞ := (rpow_lintegral_eq_top_iff ha).2 (by norm_num)

/-- Tonelli transfers a divergent cross-sectional density to every product
domain with nonzero transverse measure. -/
theorem reciprocal_shear_product_enstrophy_eq_top
    {X : Type*} [MeasurableSpace X] (nu : Measure X) [SFinite nu]
    (hnu : nu univ ≠ 0) {a : ℝ} (ha : 0 < a) :
    (∫⁻ z : ℝ × X, ENNReal.ofReal ((-(z.1 ^ 2)⁻¹) ^ 2)
      ∂(volume.restrict (Ioo (0 : ℝ) a)).prod nu) = ∞ := by
  rw [lintegral_prod_symm]
  · simp only [reciprocal_shear_enstrophy_eq_top ha, lintegral_const,
      ENNReal.top_mul hnu]
  · exact (((measurable_fst.pow_const 2).inv.neg).pow_const 2).ennreal_ofReal.aemeasurable

/-- Exact enstrophy for a spatially uniform vorticity on a unit-measure region. -/
theorem uniform_enstrophy
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (hmu : mu univ = 1) (h : ℝ) :
    (∫⁻ _ : X, ENNReal.ofReal (h ^ 2) ∂mu) = ENNReal.ofReal (h ^ 2) := by
  simp only [lintegral_const, hmu, mul_one]

/-- A general limit theorem for spatially uniform vorticity. -/
theorem uniform_enstrophy_tendsto_top
    {X I : Type*} [MeasurableSpace X] (mu : Measure X) (hmu : mu univ = 1)
    {l : Filter I} {h : I → ℝ} (hh : Tendsto h l atTop) :
    Tendsto (fun t => ∫⁻ _ : X, ENNReal.ofReal (h t ^ 2) ∂mu) l (𝓝 ∞) := by
  simp only [uniform_enstrophy mu hmu]
  exact ENNReal.tendsto_ofReal_atTop.comp ((tendsto_pow_atTop two_ne_zero).comp hh)

/-- Spatially varying vorticity also has divergent enstrophy when its square
eventually dominates an unbounded uniform square on a fixed unit-measure region. -/
theorem enstrophy_tendsto_top_of_uniform_lower_bound
    {X I : Type*} [MeasurableSpace X] (mu : Measure X) (hmu : mu univ = 1)
    {l : Filter I} {h : I → ℝ} {omega : I → X → ℝ}
    (hh : Tendsto h l atTop)
    (hbound : ∀ᶠ t in l, ∀ᵐ x ∂mu, h t ^ 2 ≤ omega t x ^ 2) :
    Tendsto (fun t => ∫⁻ x, ENNReal.ofReal (omega t x ^ 2) ∂mu) l (𝓝 ∞) := by
  apply tendsto_nhds_top_mono (uniform_enstrophy_tendsto_top mu hmu hh)
  filter_upwards [hbound] with t ht
  exact lintegral_mono_ae (ht.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))

/-- The one-sided time pole is approached only from `t < T`. -/
theorem reciprocal_time_tendsto_atTop (T : ℝ) :
    Tendsto (fun t : ℝ => (T - t)⁻¹) (𝓝[<] T) atTop := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := T) (f := 𝓝[<] T)).sub hid
  have hpos : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hzero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < T from ht)
  exact tendsto_inv_nhdsGT_zero.comp hpos

/-- A uniform reciprocal-time vorticity has diverging regional enstrophy.
PDE reconstruction and forcing regularity are separate obligations. -/
theorem reciprocal_time_enstrophy_tendsto_top
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (hmu : mu univ = 1) (T : ℝ) :
    Tendsto (fun t => ∫⁻ _ : X, ENNReal.ofReal (((T - t)⁻¹) ^ 2) ∂mu)
      (𝓝[<] T) (𝓝 ∞) :=
  uniform_enstrophy_tendsto_top mu hmu (reciprocal_time_tendsto_atTop T)

end InfoGeometry.Canonical.EnstrophyDivergence
