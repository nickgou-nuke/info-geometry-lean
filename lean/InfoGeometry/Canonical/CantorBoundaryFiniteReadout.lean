import Mathlib.Tactic
import InfoGeometry.Canonical.CantorBoundaryReadoutBounds
import InfoGeometry.Canonical.CantorBoundaryCanonical

/-!
# Finite-prefix readouts of the binary Cantor boundary

Finite prefixes are the honest colimit approximants.  This owner proves their
prefix stability and makes no global injectivity claim for infinite binary
expansions.
-/

noncomputable section

open scoped BigOperators
open scoped Topology

namespace InfoGeometry.Canonical.CantorBoundaryFiniteReadout

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryCanonical
open Set Filter

local instance : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

def realBinaryPartialReadout
    (N : ℕ) (w : InfiniteBinaryWordSpace) : ℝ :=
  ∑ n ∈ Finset.range N, realBinaryTerm w n

theorem realBinaryPartialReadout_congr_of_prefix
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (h : ∀ n < N, w n = v n) :
    realBinaryPartialReadout N w = realBinaryPartialReadout N v := by
  unfold realBinaryPartialReadout
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [realBinaryTerm]
  rw [h n (Finset.mem_range.mp hn)]

theorem realBinaryPartialReadout_zero
    (w : InfiniteBinaryWordSpace) :
    realBinaryPartialReadout 0 w = 0 := by
  simp [realBinaryPartialReadout]

theorem realBinaryPartialReadout_succ
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryPartialReadout (N + 1) w =
      realBinaryPartialReadout N w + realBinaryTerm w N := by
  unfold realBinaryPartialReadout
  rw [Finset.sum_range_succ]

theorem realBinaryPartialReadout_nonnegative
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    0 ≤ realBinaryPartialReadout N w := by
  unfold realBinaryPartialReadout
  exact Finset.sum_nonneg fun n hn => by
    dsimp [realBinaryTerm]
    split <;> positivity

theorem realBinaryPartialReadout_mono
    {N M : ℕ} (hNM : N ≤ M) (w : InfiniteBinaryWordSpace) :
    realBinaryPartialReadout N w ≤ realBinaryPartialReadout M w := by
  unfold realBinaryPartialReadout
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    (fun n hn hnot => by
      dsimp [realBinaryTerm]
      split <;> positivity)

theorem realBinaryPartialReadout_difference_at_first_difference
    {w v : InfiniteBinaryWordSpace} {k : ℕ}
    (hprefix : ∀ n < k, w n = v n)
    (hdiff : w k ≠ v k) :
    realBinaryPartialReadout (k + 1) w -
        realBinaryPartialReadout (k + 1) v =
      if w k then (1 / 2 : ℝ) ^ (k + 1)
      else -((1 / 2 : ℝ) ^ (k + 1)) := by
  have hprefix_readout :
      realBinaryPartialReadout k w = realBinaryPartialReadout k v :=
    realBinaryPartialReadout_congr_of_prefix k w v hprefix
  rw [realBinaryPartialReadout_succ, realBinaryPartialReadout_succ,
    hprefix_readout]
  cases hw : w k <;> cases hv : v k <;>
    simp [realBinaryTerm, hw, hv] at hdiff ⊢

theorem realBinaryReadout_sub_partial_le_geometricTail
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryReadout w - realBinaryPartialReadout N w ≤
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1) := by
  have hterm : ∀ n : ℕ,
      realBinaryTerm w (n + N) ≤ (1 / 2 : ℝ) ^ (n + N + 1) := by
    intro n
    dsimp [realBinaryTerm]
    split <;> simp
  have htail : Summable (fun n : ℕ => realBinaryTerm w (n + N)) :=
    (realBinaryTerm_summable w).comp_injective
      (by intro a b h; exact Nat.add_right_cancel h)
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + N + 1)) := by
    have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [Function.comp_def] using
      hs.comp_injective (i := fun n : ℕ => n + N + 1)
        (by intro a b h; exact Nat.add_right_cancel (Nat.add_right_cancel h))
  have hdecomp := (realBinaryTerm_summable w).sum_add_tsum_nat_add N
  have htail_le :
      (∑' n : ℕ, realBinaryTerm w (n + N)) ≤
        ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1) :=
    htail.tsum_le_tsum hterm hgeom
  dsimp [realBinaryReadout, realBinaryPartialReadout]
  linarith

theorem geometricTail_eq_half_pow
    (N : ℕ) :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1)) = (1 / 2 : ℝ) ^ N := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_norm_lt_one (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa [Function.comp_def] using
      hgeom.comp_injective (i := fun n : ℕ => n + 1)
        (by intro a b h; exact Nat.add_right_cancel h)
  have hshift_sum : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
    have hterm : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) =
        (fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) := by
      funext n
      rw [pow_add]
      ring
    rw [hterm, hgeom.tsum_mul_left]
    have hseries : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
      convert (tsum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)) using 1 <;>
        norm_num
    rw [hseries]
    norm_num
  have hterm : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + N + 1)) =
      (fun n : ℕ => (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (n + 1)) := by
    funext n
    rw [← pow_add]
    congr 1
    omega
  rw [hterm, hshift.tsum_mul_left, hshift_sum]
  ring

theorem realBinaryReadout_sub_partial_le_half_pow
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryReadout w - realBinaryPartialReadout N w ≤ (1 / 2 : ℝ) ^ N := by
  exact le_trans (realBinaryReadout_sub_partial_le_geometricTail N w)
    (by rw [geometricTail_eq_half_pow N])

theorem realBinaryReadout_sub_partial_lt_half_pow_of_false
    (N : ℕ) (w : InfiniteBinaryWordSpace)
    (hfalse : ∃ m ≥ N, w m = false) :
    realBinaryReadout w - realBinaryPartialReadout N w < (1 / 2 : ℝ) ^ N := by
  obtain ⟨m, hmN, hmfalse⟩ := hfalse
  let i : ℕ := m - N
  have hiN : i + N = m := by
    dsimp [i]
    exact Nat.sub_add_cancel hmN
  have htail : Summable (fun n : ℕ => realBinaryTerm w (n + N)) :=
    (realBinaryTerm_summable w).comp_injective
      (by intro a b h; exact Nat.add_right_cancel h)
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + N + 1)) := by
    have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [Function.comp_def] using
      hs.comp_injective (i := fun n : ℕ => n + N + 1)
        (by intro a b h; exact Nat.add_right_cancel (Nat.add_right_cancel h))
  have hpointwise : ∀ n : ℕ,
      realBinaryTerm w (n + N) ≤ (1 / 2 : ℝ) ^ (n + N + 1) := by
    intro n
    dsimp [realBinaryTerm]
    split <;> simp
  have hstrict :
      realBinaryTerm w (i + N) < (1 / 2 : ℝ) ^ (i + N + 1) := by
    dsimp [realBinaryTerm]
    rw [hiN, hmfalse]
    norm_num
  have htail_lt :
      (∑' n : ℕ, realBinaryTerm w (n + N)) <
        ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1) :=
    htail.tsum_lt_tsum hpointwise hstrict hgeom
  have hdecomp := (realBinaryTerm_summable w).sum_add_tsum_nat_add N
  have hgeom_eq := geometricTail_eq_half_pow N
  dsimp [realBinaryReadout, realBinaryPartialReadout]
  linarith

theorem realBinaryPartialReadout_le_readout
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryPartialReadout N w ≤ realBinaryReadout w := by
  dsimp [realBinaryPartialReadout, realBinaryReadout]
  exact (realBinaryTerm_summable w).sum_le_tsum (Finset.range N)
    (by
      intro n hn
      dsimp [realBinaryTerm]
      positivity)

theorem realBinaryPartialReadout_mem_unitInterval
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryPartialReadout N w ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact realBinaryPartialReadout_nonnegative N w
  · exact le_trans (realBinaryPartialReadout_le_readout N w)
      (realBinaryReadout_mem_unitInterval w).2

theorem realBinaryPartialReadout_tendsto_readout
    (w : InfiniteBinaryWordSpace) :
    Filter.Tendsto
      (fun N => realBinaryPartialReadout N w)
      Filter.atTop
      (nhds (realBinaryReadout w)) := by
  apply (Metric.tendsto_atTop).2
  intro ε hε
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h_lower := realBinaryPartialReadout_le_readout n w
  have h_upper := realBinaryReadout_sub_partial_le_half_pow n w
  have hpowε := hN n hn
  have hpowε' : (1 / 2 : ℝ) ^ n < ε := by
    rw [Real.dist_eq] at hpowε
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n by positivity)] using hpowε
  rw [Real.dist_eq]
  rw [abs_of_nonpos (by linarith :
    realBinaryPartialReadout n w - realBinaryReadout w ≤ 0)]
  linarith

theorem realBinaryReadout_injective_on_canonical
    {w v : InfiniteBinaryWordSpace}
    (hw : CanonicalBinaryWord w)
    (hv : CanonicalBinaryWord v)
    (hreadout : realBinaryReadout w = realBinaryReadout v) :
    w = v := by
  by_contra hne
  obtain ⟨k, hprefix, hdiff⟩ := exists_first_binary_difference hne
  have hfalse_after (u : InfiniteBinaryWordSpace)
      (hu : CanonicalBinaryWord u) :
      ∃ m ≥ k + 1, u m = false := by
    by_contra hnone
    apply hu
    refine ⟨k + 1, ?_⟩
    intro n hn
    by_contra hnot_true
    cases hbit : u n with
    | false => exact hnone ⟨n, hn, hbit⟩
    | true => exact hnot_true hbit
  have htw_nonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout (k + 1) w := by
    linarith [realBinaryPartialReadout_le_readout (k + 1) w]
  have htv_nonneg :
      0 ≤ realBinaryReadout v - realBinaryPartialReadout (k + 1) v := by
    linarith [realBinaryPartialReadout_le_readout (k + 1) v]
  have htw_le := realBinaryReadout_sub_partial_le_half_pow (k + 1) w
  have htv_le := realBinaryReadout_sub_partial_le_half_pow (k + 1) v
  cases hwk : w k with
  | false =>
      cases hvk : v k with
      | false => exact hdiff (by rw [hwk, hvk])
      | true =>
          have hdiff' : w k ≠ v k := by simp [hwk, hvk]
          have hpartial := realBinaryPartialReadout_difference_at_first_difference
            hprefix hdiff'
          have hpartial' :
              realBinaryPartialReadout (k + 1) w -
                realBinaryPartialReadout (k + 1) v =
                -((1 / 2 : ℝ) ^ (k + 1)) := by
            simpa [hwk] using hpartial
          have hpow : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
          have htw_strict := realBinaryReadout_sub_partial_lt_half_pow_of_false
            (k + 1) w (hfalse_after w hw)
          have hbalance :
              realBinaryReadout w - realBinaryPartialReadout (k + 1) w =
                (realBinaryReadout v - realBinaryPartialReadout (k + 1) v) +
                  (1 / 2 : ℝ) ^ (k + 1) := by
            linarith [hreadout, hpartial']
          linarith
  | true =>
      cases hvk : v k with
      | false =>
          have hdiff' : v k ≠ w k := by simp [hwk, hvk]
          have hprefix' : ∀ n < k, v n = w n := by
            intro n hn
            exact (hprefix n hn).symm
          have hpartial := realBinaryPartialReadout_difference_at_first_difference
            hprefix' hdiff'
          have hpartial' :
              realBinaryPartialReadout (k + 1) v -
                realBinaryPartialReadout (k + 1) w =
                -((1 / 2 : ℝ) ^ (k + 1)) := by
            simpa [hvk] using hpartial
          have htw_strict := realBinaryReadout_sub_partial_lt_half_pow_of_false
            (k + 1) w (hfalse_after w hw)
          have htv_strict := realBinaryReadout_sub_partial_lt_half_pow_of_false
            (k + 1) v (hfalse_after v hv)
          have hpow : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
          have hbalance :
              realBinaryReadout v - realBinaryPartialReadout (k + 1) v =
                (realBinaryReadout w - realBinaryPartialReadout (k + 1) w) +
                  (1 / 2 : ℝ) ^ (k + 1) := by
            linarith [hreadout, hpartial']
          linarith
      | true => exact hdiff (by rw [hwk, hvk])

/-- The canonical readout is injective on the canonical-word subtype. -/
theorem realBinaryReadout_injective_on_canonicalSpace :
    Function.Injective
      (fun w : {w : InfiniteBinaryWordSpace // CanonicalBinaryWord w} =>
        realBinaryReadout w.val) := by
  intro w v hreadout
  apply Subtype.ext
  exact realBinaryReadout_injective_on_canonical w.property v.property hreadout

theorem abs_realBinaryReadout_sub_le_of_prefix
    (N : ℕ) (w v : InfiniteBinaryWordSpace)
    (hprefix : ∀ n < N, w n = v n) :
    |realBinaryReadout w - realBinaryReadout v| ≤ (1 / 2 : ℝ) ^ N := by
  have hpartial :
      realBinaryPartialReadout N w = realBinaryPartialReadout N v :=
    realBinaryPartialReadout_congr_of_prefix N w v hprefix
  have hw_nonneg :
      0 ≤ realBinaryReadout w - realBinaryPartialReadout N w := by
    linarith [realBinaryPartialReadout_le_readout N w]
  have hv_nonneg :
      0 ≤ realBinaryReadout v - realBinaryPartialReadout N v := by
    linarith [realBinaryPartialReadout_le_readout N v]
  have hw_le := realBinaryReadout_sub_partial_le_half_pow N w
  have hv_le := realBinaryReadout_sub_partial_le_half_pow N v
  rw [abs_le]
  constructor <;> linarith [hpartial]

theorem realBinaryReadout_lt_one_of_canonical
    (w : InfiniteBinaryWordSpace) (hw : CanonicalBinaryWord w) :
    realBinaryReadout w < 1 := by
  have hfalse : ∃ m ≥ 0, w m = false := by
    by_contra hnone
    apply hw
    refine ⟨0, ?_⟩
    intro n hn
    by_contra hnot_true
    cases hbit : w n with
    | false => exact hnone ⟨n, Nat.zero_le n, hbit⟩
    | true => exact hnot_true hbit
  have hstrict := realBinaryReadout_sub_partial_lt_half_pow_of_false 0 w hfalse
  have hzero := realBinaryPartialReadout_zero w
  norm_num [hzero] at hstrict ⊢
  linarith

theorem realBinaryReadout_lt_one_on_canonicalSpace
    (w : {w : InfiniteBinaryWordSpace // CanonicalBinaryWord w}) :
    realBinaryReadout w.val < 1 :=
  realBinaryReadout_lt_one_of_canonical w.val w.property

theorem continuous_realBinaryPartialReadout
    (N : ℕ) :
    Continuous (fun w : InfiniteBinaryWordSpace => realBinaryPartialReadout N w) := by
  unfold realBinaryPartialReadout
  apply continuous_finset_sum
  intro n hn
  unfold realBinaryTerm
  have hbool : Continuous (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
    continuous_of_discreteTopology
  have hterm : Continuous (fun w : InfiniteBinaryWordSpace =>
      if w n = true then (1 : ℝ) else 0) :=
    hbool.comp (continuous_apply n)
  exact hterm.mul continuous_const

theorem continuous_realBinaryReadout :
    Continuous (fun w : InfiniteBinaryWordSpace => realBinaryReadout w) := by
  rw [continuous_iff_continuousAt]
  intro w
  change Tendsto realBinaryReadout (𝓝 w) (𝓝 (realBinaryReadout w))
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hball⟩ := hs
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  let C : Set InfiniteBinaryWordSpace :=
    ⋂ n ∈ Finset.range N, {v | v n = w n}
  have hCopen : IsOpen C := by
    apply isOpen_biInter_finset
    intro n hn
    change IsOpen ((fun v : InfiniteBinaryWordSpace => v n) ⁻¹' ({w n} : Set Bool))
    apply (continuous_apply n).isOpen_preimage
    exact isOpen_discrete _
  have hwC : w ∈ C := by
    simp [C]
  have hCnhds : C ∈ 𝓝 w := hCopen.mem_nhds hwC
  have hsubset : C ⊆ realBinaryReadout ⁻¹' Metric.ball (realBinaryReadout w) ε := by
    intro v hv
    have hpref : ∀ n < N, v n = w n := by
      intro n hn
      have hn' : n ∈ Finset.range N := Finset.mem_range.mpr hn
      have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp hv n) hn'
      exact hmem
    have hbound := abs_realBinaryReadout_sub_le_of_prefix N v w hpref
    have hpowε : (1 / 2 : ℝ) ^ N < ε := by
      have hN' := hN N (le_rfl)
      rw [Real.dist_eq] at hN'
      simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)] using hN'
    rw [Set.mem_preimage, Metric.mem_ball]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hbound hpowε
  have hsubset' : C ⊆ realBinaryReadout ⁻¹' s := by
    intro v hv
    exact hball (hsubset hv)
  show realBinaryReadout ⁻¹' s ∈ 𝓝 w
  exact mem_of_superset hCnhds hsubset'

theorem realBinaryReadout_boundaryCons
    (a : Bool) (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (boundaryCons a w) =
      (if a then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * realBinaryReadout w := by
  have hsum := (realBinaryTerm_summable (boundaryCons a w)).sum_add_tsum_nat_add 1
  have htail : (∑' n : ℕ, realBinaryTerm (boundaryCons a w) (n + 1)) =
      (1 / 2 : ℝ) * realBinaryReadout w := by
    change (∑' n : ℕ, realBinaryTerm (boundaryCons a w) (n + 1)) =
      (1 / 2 : ℝ) * (∑' n : ℕ, realBinaryTerm w n)
    rw [← (realBinaryTerm_summable w).tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [realBinaryTerm, boundaryCons]
    simp only [Nat.add_assoc, Nat.add_comm n 1]
    rw [pow_add]
    split <;> simp
  change (∑' n : ℕ, realBinaryTerm (boundaryCons a w) n) = _
  rw [← hsum]
  rw [htail]
  norm_num [realBinaryTerm, boundaryCons]

theorem realBinaryReadout_boundaryTail
    (w : InfiniteBinaryWordSpace) :
    (1 / 2 : ℝ) * realBinaryReadout (boundaryTail w) =
      realBinaryReadout w -
        (if boundaryHead w then (1 / 2 : ℝ) else 0) := by
  have hrec := realBinaryReadout_boundaryCons (boundaryHead w) (boundaryTail w)
  rw [← boundary_recursive_decomposition w] at hrec
  linarith

def finitePrefixReadout : List Bool → ℝ
  | [] => 0
  | b :: bs =>
      (if b then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * finitePrefixReadout bs

theorem realBinaryReadout_boundaryConsList
    (bs : List Bool) (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (boundaryConsList bs w) =
      finitePrefixReadout bs +
        (1 / 2 : ℝ) ^ bs.length * realBinaryReadout w := by
  induction bs with
  | nil =>
      simp [finitePrefixReadout, boundaryConsList]
  | cons b bs ih =>
      rw [boundaryConsList_cons, realBinaryReadout_boundaryCons, ih]
      simp only [finitePrefixReadout, List.length_cons]
      ring_nf

theorem realBinaryReadout_prefix_tail_decomposition
    (N : ℕ) (w : InfiniteBinaryWordSpace) :
    realBinaryReadout w =
      finitePrefixReadout (boundaryPrefix N w) +
        (1 / 2 : ℝ) ^ N *
          realBinaryReadout (boundaryIterateTail N w) := by
  conv_lhs => rw [boundary_iterated_decomposition N w]
  rw [realBinaryReadout_boundaryConsList, boundaryPrefix_length]

end InfoGeometry.Canonical.CantorBoundaryFiniteReadout
