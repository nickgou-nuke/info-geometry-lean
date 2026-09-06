import InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import InfoGeometry.Canonical.CantorProjectiveReadoutBridge
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Finite-prefix readouts on the projective limit

Finite prefix words carry finite readout observables.  This owner packages
those observables as `TopCat` maps and composes them with the coherent-prefix
projections.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
open InfoGeometry.Canonical.CantorProjectiveReadoutBridge

def finitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of (BitWord n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun w => finitePrefixReadout (List.ofFn w)
      continuous_toFun := by fun_prop }

def projectiveFinitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  projectiveProjectionTopCatHom n ≫ finitePrefixReadoutTopCatHom n

@[simp] theorem finitePrefixReadoutTopCatHom_apply
    (n : ℕ) (w : BitWord n) :
    finitePrefixReadoutTopCatHom n w = finitePrefixReadout (List.ofFn w) := rfl

@[simp] theorem projectiveFinitePrefixReadoutTopCatHom_apply
    (n : ℕ) (p : PrefixProjectiveLimit) :
    projectiveFinitePrefixReadoutTopCatHom n p =
      finitePrefixReadout (List.ofFn (π n p)) := by
  rfl

theorem projectiveFinitePrefixReadout_cantor_compatibility
    (n : ℕ) (x : (ℕ → Bool)) :
    projectiveFinitePrefixReadoutTopCatHom n
        (cantorProjectiveLimitTopCatIso.hom x) =
      finitePrefixReadout (List.ofFn (boundaryPrefix n x)) := by
  change (projectiveProjectionTopCatHom n ≫
      finitePrefixReadoutTopCatHom n)
      (cantorProjectiveLimitTopCatIso.hom x) = _
  rw [TopCat.comp_app]
  change finitePrefixReadout
      (List.ofFn (π n (cantorProjectiveLimitTopCatIso.hom x))) = _
  have h := cantorProjectiveLimit_projection_readout n x
  exact congrArg (fun w => finitePrefixReadout (List.ofFn w)) h

theorem projectiveFinitePrefixReadout_error_bound
    (n : ℕ) (p : PrefixProjectiveLimit) :
    realBinaryReadout (toCantor p) -
        projectiveFinitePrefixReadoutTopCatHom n p ≤
      (1 / 2 : ℝ) ^ n := by
  rw [projectiveFinitePrefixReadoutTopCatHom_apply]
  change realBinaryReadout (toCantor p) -
      finitePrefixReadout (List.ofFn (p.word n)) ≤
    (1 / 2 : ℝ) ^ n
  rw [← boundaryPrefix_toCantor_eq_word p n]
  rw [bitWordPrefix_list_eq]
  rw [finitePrefixReadout_boundaryPrefix]
  exact realBinaryReadout_sub_partial_le_half_pow n (toCantor p)

theorem projectiveFinitePrefixReadout_abs_error_bound
    (n : ℕ) (p : PrefixProjectiveLimit) :
    |realBinaryReadout (toCantor p) -
        projectiveFinitePrefixReadoutTopCatHom n p| ≤
      (1 / 2 : ℝ) ^ n := by
  have hnonneg :
      0 ≤ realBinaryReadout (toCantor p) -
        projectiveFinitePrefixReadoutTopCatHom n p := by
    rw [projectiveFinitePrefixReadoutTopCatHom_apply]
    change 0 ≤ realBinaryReadout (toCantor p) -
      finitePrefixReadout (List.ofFn (p.word n))
    rw [← boundaryPrefix_toCantor_eq_word p n, bitWordPrefix_list_eq,
      finitePrefixReadout_boundaryPrefix]
    exact sub_nonneg.mpr
      (realBinaryPartialReadout_le_readout n (toCantor p))
  rw [abs_of_nonneg hnonneg]
  exact projectiveFinitePrefixReadout_error_bound n p

theorem projectiveFinitePrefixReadout_uniform_tendsto :
    TendstoUniformly
      (fun n p => projectiveFinitePrefixReadoutTopCatHom n p)
      (fun p => realBinaryReadout (toCantor p)) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  intro p
  rw [Real.dist_eq, abs_sub_comm]
  have hbound :
      |projectiveFinitePrefixReadoutTopCatHom n p -
          realBinaryReadout (toCantor p)| ≤ (2 ^ n : ℝ)⁻¹ := by
    have habs := projectiveFinitePrefixReadout_abs_error_bound n p
    rw [abs_sub_comm] at habs
    simpa [one_div, inv_pow] using habs
  exact lt_of_le_of_lt hbound
    (by
      have hpowN := hN n hn
      rw [Real.dist_eq] at hpowN
      simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n by positivity)]
        using hpowN)

theorem projectiveFinitePrefixReadout_tendsto
    (p : PrefixProjectiveLimit) :
    Filter.Tendsto
      (fun n => projectiveFinitePrefixReadoutTopCatHom n p)
      Filter.atTop
      (nhds (realBinaryReadout (toCantor p))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq]
  have hbound :
      |projectiveFinitePrefixReadoutTopCatHom n p -
          realBinaryReadout (toCantor p)| ≤ (2 ^ n : ℝ)⁻¹ := by
    have habs := projectiveFinitePrefixReadout_abs_error_bound n p
    rw [abs_sub_comm] at habs
    simpa [one_div, inv_pow] using habs
  exact lt_of_le_of_lt hbound
    (by
      have hpowN := hN n hn
      rw [Real.dist_eq] at hpowN
      simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n by positivity)]
        using hpowN)

end InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat
