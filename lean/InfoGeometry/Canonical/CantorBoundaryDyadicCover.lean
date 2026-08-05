import InfoGeometry.Canonical.CantorBoundaryReadoutDyadicRange
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Finite dyadic cover of the unit interval

Every point of `[0,1]` lies in a binary dyadic interval at every finite
depth.  This is the finite branch-selection layer; it does not yet choose a
single compatible infinite branch.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.CantorBoundaryDyadicCover

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryReadoutDyadicRange
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

def prependBit {n : ℕ} (b : Bool) (w : BitWord n) : BitWord (n + 1) :=
  fun i => if h : i.1 = 0 then b else w ⟨i.1 - 1, by
    have hi := i.isLt
    have hpos : 0 < i.1 := Nat.pos_of_ne_zero h
    omega⟩

theorem list_ofFn_prependBit {n : ℕ} (b : Bool) (w : BitWord n) :
    List.ofFn (prependBit b w) = b :: List.ofFn w := by
  simp [List.ofFn_succ, prependBit]

theorem finitePrefixReadout_prependBit {n : ℕ} (b : Bool) (w : BitWord n) :
    finitePrefixReadout (List.ofFn (prependBit b w)) =
      (if b then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * finitePrefixReadout (List.ofFn w) := by
  rw [list_ofFn_prependBit]
  rfl

theorem finitePrefixReadout_add_pow_le_one (bs : List Bool) :
    finitePrefixReadout bs + (1 / 2 : ℝ) ^ bs.length ≤ 1 := by
  induction bs with
  | nil => norm_num [finitePrefixReadout]
  | cons b bs ih =>
      cases b <;> simp [finitePrefixReadout, pow_succ] at * <;>
        nlinarith

theorem prefix_interval_subset_unitInterval
    {n : ℕ} (w : BitWord n) :
    Set.Icc
        (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) ⊆
      Set.Icc (0 : ℝ) 1 := by
  intro x hx
  have hnonneg : 0 ≤ finitePrefixReadout (List.ofFn w) :=
    finitePrefixReadout_nonnegative (List.ofFn w)
  have hupper :
      finitePrefixReadout (List.ofFn w) +
          (1 / 2 : ℝ) ^ (List.ofFn w).length ≤ 1 :=
    finitePrefixReadout_add_pow_le_one (List.ofFn w)
  have hlength : (List.ofFn w).length = n := by
    simp
  rw [hlength] at hupper
  exact ⟨le_trans hnonneg hx.1, hx.2.trans hupper⟩

theorem exists_prefix_dyadic_cover
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∃ w : BitWord n,
      x ∈ Set.Icc
        (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) := by
  induction n generalizing x with
  | zero =>
      refine ⟨fun i => i.elim0, ?_⟩
      simpa [finitePrefixReadout] using hx
  | succ n ih =>
      by_cases hhalf : x ≤ (1 / 2 : ℝ)
      · have hy : 2 * x ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [hx.1, hhalf]
        obtain ⟨w, hw⟩ := ih (2 * x) hy
        refine ⟨prependBit false w, ?_⟩
        rw [finitePrefixReadout_prependBit]
        simp
        have hpow : (2 ^ (n + 1) : ℝ)⁻¹ =
            (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          calc
            (2 ^ (n + 1) : ℝ)⁻¹ = ((2 : ℝ)⁻¹) ^ (n + 1) := by
              rw [← inv_pow]
            _ = (1 / 2 : ℝ) ^ (n + 1) := by norm_num
            _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
              rw [pow_succ]
              ring
        rw [hpow]
        constructor <;> nlinarith [hw.1, hw.2]
      · have hhalf' : (1 / 2 : ℝ) < x := lt_of_not_ge hhalf
        have hy : 2 * x - 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [hx.2, hhalf']
        obtain ⟨w, hw⟩ := ih (2 * x - 1) hy
        refine ⟨prependBit true w, ?_⟩
        rw [finitePrefixReadout_prependBit]
        simp
        have hpow : (2 ^ (n + 1) : ℝ)⁻¹ =
            (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          calc
            (2 ^ (n + 1) : ℝ)⁻¹ = ((2 : ℝ)⁻¹) ^ (n + 1) := by
              rw [← inv_pow]
            _ = (1 / 2 : ℝ) ^ (n + 1) := by norm_num
            _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
              rw [pow_succ]
              ring
        rw [hpow]
        constructor <;> nlinarith [hw.1, hw.2]

theorem exists_realBinaryReadout_close
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : InfiniteBinaryWordSpace,
      |x - realBinaryReadout w| < ε := by
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    have hN' := hN N (le_rfl)
    rw [Real.dist_eq] at hN'
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)] using hN'
  obtain ⟨wN, hwN⟩ := exists_prefix_dyadic_cover x hx N
  obtain ⟨w, hw⟩ := finitePrefixReadout_mem_realBinaryReadout_range
    (List.ofFn wN)
  refine ⟨w, ?_⟩
  rw [hw]
  rw [abs_of_nonneg (by linarith [hwN.1])]
  linarith [hwN.2, hpowN]

end InfoGeometry.Canonical.CantorBoundaryDyadicCover
