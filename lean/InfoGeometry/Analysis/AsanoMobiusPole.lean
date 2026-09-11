import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LeeYangAsanoNondegeneratePrep

/-!
# The Möbius pole in the Asano contraction

For a nondegenerate multiaffine polynomial, the second-coordinate root map

`z ↦ -(A + B*z) / (C + D*z)`

escapes every bounded subset of `ℂ` as `z` approaches its pole `-C/D`
through the punctured neighborhood.  This is the reusable filter-theoretic
core of the bounded Asano--Ruelle endpoint argument.
-/

noncomputable section

namespace InfoGeometry.Analysis.AsanoMobiusPole

open Filter Set Topology
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-- The denominator of the Asano root map vanishes at `-C/D`. -/
theorem denominator_at_pole
    {C D : ℂ}
    (hD : D ≠ 0) :
    C + D * (-(C / D)) = 0 := by
  field_simp [hD]
  ring

/-- Away from the pole, the denominator of the root map is nonzero. -/
theorem denominator_ne_zero_off_pole
    {C D z : ℂ}
    (hD : D ≠ 0)
    (hz : z ≠ -(C / D)) :
    C + D * z ≠ 0 := by
  intro hden
  apply hz
  have hDz : D * z = -C :=
    eq_neg_of_add_eq_zero_right hden
  calc
    z = (D * z) / D := by
      field_simp [hD]
    _ = -C / D := by rw [hDz]
    _ = -(C / D) := by ring

/--
The reciprocal denominator norm tends to `+∞` at the punctured pole.
-/
theorem inv_norm_denominator_tendsto_atTop
    {C D : ℂ}
    (hD : D ≠ 0) :
    Tendsto
      (fun z : ℂ => ‖C + D * z‖⁻¹)
      (nhdsWithin (-(C / D)) {-(C / D)}ᶜ)
      atTop := by
  let p : ℂ := -(C / D)
  have hp : C + D * p = 0 := by
    simpa [p] using denominator_at_pole (C := C) hD
  have hden :
      Tendsto (fun z : ℂ => C + D * z) (nhdsWithin p {p}ᶜ) (nhds 0) := by
    have hfull :
        Tendsto (fun z : ℂ => C + D * z) (nhds p) (nhds (C + D * p)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [hp] at hfull
    exact hfull.mono_left nhdsWithin_le_nhds
  have hnorm :
      Tendsto (fun z : ℂ => ‖C + D * z‖) (nhdsWithin p {p}ᶜ) (nhds 0) := by
    simpa using hden.norm
  have hpos :
      ∀ᶠ z : ℂ in nhdsWithin p {p}ᶜ, 0 < ‖C + D * z‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pos_iff.mpr
      (denominator_ne_zero_off_pole hD (by simpa [p] using hz))
  exact tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hnorm, hpos⟩)

/--
The Asano Möbius root map tends to the cobounded filter at its pole.
-/
theorem asanoRootMap_tendsto_cobounded
    {A B C D : ℂ}
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0) :
    Tendsto
      (asanoRootMap A B C D)
      (nhdsWithin (-(C / D)) {-(C / D)}ᶜ)
      (Bornology.cobounded ℂ) := by
  let p : ℂ := -(C / D)
  let c : ℝ := ‖A + B * p‖
  have hnum_ne : A + B * p ≠ 0 := by
    apply rootMap_pole_not_numerator_zero hNondeg
    simpa [p] using denominator_at_pole (C := C) hD
  have hc : 0 < c := by
    exact norm_pos_iff.mpr hnum_ne
  have hnum :
      Tendsto (fun z : ℂ => ‖A + B * z‖) (nhdsWithin p {p}ᶜ) (nhds c) := by
    have hfull :
        Tendsto (fun z : ℂ => A + B * z) (nhds p) (nhds (A + B * p)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    exact (hfull.mono_left nhdsWithin_le_nhds).norm
  have hnum_lower :
      ∀ᶠ z : ℂ in nhdsWithin p {p}ᶜ, c / 2 ≤ ‖A + B * z‖ := by
    apply hnum.eventually
    filter_upwards [Ioi_mem_nhds (half_lt_self hc)] with x hx
    exact le_of_lt hx
  have hinv :
      Tendsto (fun z : ℂ => ‖C + D * z‖⁻¹) (nhdsWithin p {p}ᶜ) atTop := by
    simpa [p] using inv_norm_denominator_tendsto_atTop (C := C) hD
  have hlower :
      Tendsto
        (fun z : ℂ => (c / 2) * ‖C + D * z‖⁻¹)
        (nhdsWithin p {p}ᶜ)
        atTop :=
    hinv.const_mul_atTop (half_pos hc)
  have hratio :
      Tendsto
        (fun z : ℂ => ‖A + B * z‖ * ‖C + D * z‖⁻¹)
        (nhdsWithin p {p}ᶜ)
        atTop := by
    have hprod_lower :
        ∀ᶠ z : ℂ in nhdsWithin p {p}ᶜ,
          (c / 2) * ‖C + D * z‖⁻¹ ≤
            ‖A + B * z‖ * ‖C + D * z‖⁻¹ := by
      filter_upwards [hnum_lower] with z hz
      exact mul_le_mul_of_nonneg_right hz (inv_nonneg.mpr (norm_nonneg _))
    exact tendsto_atTop_mono' _ hprod_lower hlower
  apply tendsto_norm_atTop_iff_cobounded.mp
  simpa [asanoRootMap, p, norm_div, div_eq_mul_inv] using hratio

/--
A function tending to the cobounded filter cannot be eventually contained in
a bounded set.
-/
theorem not_eventually_mem_bounded_of_tendsto_cobounded
    {f : ℂ → ℂ}
    {l : Filter ℂ}
    [l.NeBot]
    {K : Set ℂ}
    (hf : Tendsto f l (Bornology.cobounded ℂ))
    (hK : Bornology.IsBounded K) :
    ¬ ∀ᶠ z in l, f z ∈ K := by
  intro hmem
  rcases (Metric.isBounded_iff_subset_ball 0).mp hK with ⟨M, hKM⟩
  have hlt : ∀ᶠ z in l, ‖f z‖ < M := by
    filter_upwards [hmem] with z hz
    have := hKM hz
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hnorm : Tendsto (fun z => ‖f z‖) l atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr hf
  have hge : ∀ᶠ z in l, M ≤ ‖f z‖ :=
    hnorm.eventually (eventually_ge_atTop M)
  have hfalse : ∀ᶠ _z in l, False := by
    filter_upwards [hlt, hge] with z hzlt hzge
    exact (not_lt_of_ge hzge) hzlt
  rcases hfalse.exists with ⟨z, hz⟩
  exact hz

/--
The Asano root map cannot remain in a bounded set throughout a punctured
neighborhood of its nondegenerate pole.
-/
theorem asanoRootMap_not_eventually_mem_bounded
    {A B C D : ℂ}
    {K : Set ℂ}
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK : Bornology.IsBounded K) :
    ¬ ∀ᶠ z in nhdsWithin (-(C / D)) {-(C / D)}ᶜ,
      asanoRootMap A B C D z ∈ K :=
  not_eventually_mem_bounded_of_tendsto_cobounded
    (asanoRootMap_tendsto_cobounded hD hNondeg) hK

end InfoGeometry.Analysis.AsanoMobiusPole
