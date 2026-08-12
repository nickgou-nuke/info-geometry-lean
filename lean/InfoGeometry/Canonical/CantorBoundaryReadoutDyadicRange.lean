import InfoGeometry.Canonical.CantorBoundaryFiniteReadout

/-!
# Dyadic endpoints in the binary readout range

Finite binary prefixes give genuine points of the infinite readout range by
choosing the all-false tail.  This is a concrete approximation theorem; it is
not a surjectivity theorem for the whole unit interval.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.CantorBoundaryReadoutDyadicRange

open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

theorem finitePrefixReadout_nonnegative (bs : List Bool) :
    0 ≤ finitePrefixReadout bs := by
  induction bs with
  | nil => simp [finitePrefixReadout]
  | cons b bs ih =>
      cases b <;> simp [finitePrefixReadout, ih] <;> positivity

theorem finitePrefixReadout_le_one (bs : List Bool) :
    finitePrefixReadout bs ≤ 1 := by
  induction bs with
  | nil => simp [finitePrefixReadout]
  | cons b bs ih =>
      cases b <;> simp [finitePrefixReadout] at * <;> linarith

theorem finitePrefixReadout_mem_unitInterval (bs : List Bool) :
    finitePrefixReadout bs ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finitePrefixReadout_nonnegative bs, finitePrefixReadout_le_one bs⟩

theorem realBinaryReadout_allFalse :
    realBinaryReadout (fun _ : ℕ => false) = 0 := by
  simp [realBinaryReadout, realBinaryTerm]

theorem realBinaryReadout_allTrue :
    realBinaryReadout (fun _ : ℕ => true) = 1 := by
  have h := realBinaryReadout_complement (fun _ : ℕ => false)
  simpa [realBinaryReadout_allFalse] using h

theorem realBinaryReadout_range_reflection (w : ℕ → Bool) :
    1 - realBinaryReadout w ∈ Set.range realBinaryReadout := by
  refine ⟨fun n => !w n, ?_⟩
  exact realBinaryReadout_complement_eq_one_sub w

theorem finitePrefixReadout_mem_realBinaryReadout_range
    (bs : List Bool) :
    finitePrefixReadout bs ∈ Set.range realBinaryReadout := by
  refine ⟨boundaryConsList bs (fun _ : ℕ => false), ?_⟩
  rw [realBinaryReadout_boundaryConsList, realBinaryReadout_allFalse]
  simp

theorem exists_finitePrefixReadout_close
    (w : (ℕ → Bool)) {ε : ℝ} (hε : 0 < ε) :
  ∃ bs : List Bool,
      |realBinaryReadout w - finitePrefixReadout bs| < ε := by
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    have hN' := hN N (le_rfl)
    rw [Real.dist_eq] at hN'
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)] using hN'
  refine ⟨boundaryPrefix N w, ?_⟩
  have hdecomp := realBinaryReadout_prefix_tail_decomposition N w
  have htail :=
    realBinaryReadout_mem_unitInterval (boundaryIterateTail N w)
  have hp : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  rw [hdecomp]
  have hprod_nonneg :
      0 ≤ (1 / 2 : ℝ) ^ N * realBinaryReadout (boundaryIterateTail N w) :=
    mul_nonneg hp htail.1
  have hprod_le :
      (1 / 2 : ℝ) ^ N * realBinaryReadout (boundaryIterateTail N w)
        ≤ (1 / 2 : ℝ) ^ N := by
    calc
      (1 / 2 : ℝ) ^ N * realBinaryReadout (boundaryIterateTail N w)
          ≤ (1 / 2 : ℝ) ^ N * 1 :=
        mul_le_mul_of_nonneg_left htail.2 hp
      _ = (1 / 2 : ℝ) ^ N := by ring
  have hdiff_nonneg :
      0 ≤ finitePrefixReadout (boundaryPrefix N w) +
          (1 / 2 : ℝ) ^ N * realBinaryReadout (boundaryIterateTail N w) -
          finitePrefixReadout (boundaryPrefix N w) := by
    linarith
  rw [abs_of_nonneg hdiff_nonneg]
  linarith

theorem realBinaryReadout_mem_closure_finitePrefixReadout
    (w : ℕ → Bool) :
    realBinaryReadout w ∈ closure (Set.range finitePrefixReadout) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨bs, hbs⟩ := exists_finitePrefixReadout_close w hε
  refine ⟨finitePrefixReadout bs, ⟨bs, rfl⟩, ?_⟩
  simpa [Real.dist_eq] using hbs

theorem tendsto_finitePrefixReadout_boundaryPrefix
    (w : ℕ → Bool) :
    Filter.Tendsto
      (fun n => finitePrefixReadout (boundaryPrefix n w))
      Filter.atTop (𝓝 (realBinaryReadout w)) := by
  apply (Metric.tendsto_atTop.2)
  intro ε hε
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hdecomp := realBinaryReadout_prefix_tail_decomposition n w
  have htail := realBinaryReadout_mem_unitInterval (boundaryIterateTail n w)
  have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hprod_nonneg :
      0 ≤ (1 / 2 : ℝ) ^ n * realBinaryReadout (boundaryIterateTail n w) :=
    mul_nonneg hp htail.1
  have hprod_le :
      (1 / 2 : ℝ) ^ n * realBinaryReadout (boundaryIterateTail n w)
        ≤ (1 / 2 : ℝ) ^ n := by
    calc
      (1 / 2 : ℝ) ^ n * realBinaryReadout (boundaryIterateTail n w)
          ≤ (1 / 2 : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left htail.2 hp
      _ = (1 / 2 : ℝ) ^ n := by ring
  have hpow_lt : (1 / 2 : ℝ) ^ n < ε := by
    have h := hN n hn
    rw [Real.dist_eq] at h
    simpa [abs_of_nonneg hp] using h
  rw [Real.dist_eq, hdecomp]
  have hdiff :
      finitePrefixReadout (boundaryPrefix n w) -
          (finitePrefixReadout (boundaryPrefix n w) +
            (1 / 2 : ℝ) ^ n * realBinaryReadout (boundaryIterateTail n w)) =
        -((1 / 2 : ℝ) ^ n * realBinaryReadout (boundaryIterateTail n w)) := by
    ring
  rw [hdiff, abs_neg, abs_of_nonneg hprod_nonneg]
  exact lt_of_le_of_lt hprod_le hpow_lt

end InfoGeometry.Canonical.CantorBoundaryReadoutDyadicRange
