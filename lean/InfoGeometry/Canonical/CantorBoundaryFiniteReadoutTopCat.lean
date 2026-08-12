import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# TopCat finite readout approximants

The finite binary partial readouts are continuous cylinder observables.  This
owner exposes them as `TopCat` arrows and records the existing geometric-tail
error bound, without adding a completion or measure-theoretic limit.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.CantorBoundaryFiniteReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

def realBinaryPartialReadoutTopCatHom (N : ℕ) :
    TopCat.of (ℕ → Bool) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun w => realBinaryPartialReadout N w
      continuous_toFun := continuous_realBinaryPartialReadout N }

@[simp] theorem realBinaryPartialReadoutTopCatHom_apply
    (N : ℕ) (w : (ℕ → Bool)) :
    realBinaryPartialReadoutTopCatHom N w = realBinaryPartialReadout N w := rfl

theorem realBinaryPartialReadout_prefixBit
    (N : ℕ) (b : Bool) (w : (ℕ → Bool)) :
    realBinaryPartialReadout (N + 1) (prefixBit b w) =
      (if b then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * realBinaryPartialReadout N w := by
  induction N with
  | zero =>
      simp [realBinaryPartialReadout_succ, realBinaryPartialReadout_zero,
        realBinaryTerm, prefixBit]
  | succ N ih =>
      rw [realBinaryPartialReadout_succ, ih]
      rw [realBinaryPartialReadout_succ]
      have hterm :
          realBinaryTerm (prefixBit b w) (N + 1) =
            (1 / 2 : ℝ) * realBinaryTerm w N := by
        by_cases h : w N
        · simp [realBinaryTerm, prefixBit, h]
          ring
        · simp [realBinaryTerm, prefixBit, h]
      rw [hterm]
      ring

theorem realBinaryPartialReadoutTopCatHom_error_bound
    (N : ℕ) (w : (ℕ → Bool)) :
    realBinaryReadout w - realBinaryPartialReadoutTopCatHom N w ≤
      (1 / 2 : ℝ) ^ N := by
  exact realBinaryReadout_sub_partial_le_half_pow N w

theorem realBinaryPartialReadoutTopCatHom_abs_error_bound
    (N : ℕ) (w : (ℕ → Bool)) :
    |realBinaryReadout w - realBinaryPartialReadoutTopCatHom N w| ≤
      (1 / 2 : ℝ) ^ N := by
  have hnonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout N w :=
    sub_nonneg.mpr (realBinaryPartialReadout_le_readout N w)
  simpa [realBinaryPartialReadoutTopCatHom, abs_of_nonneg hnonneg] using
    realBinaryReadout_sub_partial_le_half_pow N w

theorem realBinaryPartialReadout_tendsto
    (w : (ℕ → Bool)) :
    Filter.Tendsto (fun N => realBinaryPartialReadout N w) Filter.atTop
      (𝓝 (realBinaryReadout w)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hnonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout N w :=
    sub_nonneg.mpr (realBinaryPartialReadout_le_readout N w)
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)]
      using hN₀ N hN
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt
    (realBinaryReadout_sub_partial_le_half_pow N w)
    hpowN

theorem realBinaryPartialReadout_uniform_tendsto :
    TendstoUniformly
      (fun N w => realBinaryPartialReadout N w)
      realBinaryReadout Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N₀, fun N hN => hN⟩] with N hN
  intro w
  have hnonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout N w :=
    sub_nonneg.mpr (realBinaryPartialReadout_le_readout N w)
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    simpa [Real.dist_eq,
      abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)]
      using hN₀ N hN
  rw [Real.dist_eq, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt
    (realBinaryReadout_sub_partial_le_half_pow N w)
    hpowN

end InfoGeometry.Canonical.CantorBoundaryFiniteReadoutTopCat
