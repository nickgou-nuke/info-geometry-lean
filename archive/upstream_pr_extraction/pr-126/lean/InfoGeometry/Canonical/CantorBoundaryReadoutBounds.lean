import Mathlib.Tactic
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Real bounds for the binary Cantor readout

This file proves the elementary unit-interval bounds for the real binary
geometric readout.  It makes no injectivity claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutBounds

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

def realBinaryTerm (w : (ℕ → Bool)) (n : ℕ) : ℝ :=
  (if w n then 1 else 0) * (1 / 2 : ℝ) ^ (n + 1)

theorem realBinaryTerm_complement_add
    (w : (ℕ → Bool)) (n : ℕ) :
    realBinaryTerm (fun k => !w k) n + realBinaryTerm w n =
      (1 / 2 : ℝ) ^ (n + 1) := by
  dsimp [realBinaryTerm]
  cases h : w n <;> simp [h]

theorem realBinaryTerm_summable (w : (ℕ → Bool)) :
    Summable (realBinaryTerm w) := by
  apply Summable.of_norm_bounded (f := realBinaryTerm w)
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  · have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
      exact summable_geometric_of_norm_lt_one (by norm_num)
    simpa [Function.comp_def] using
      hgeom.comp_injective (i := fun n : ℕ => n + 1)
        (by intro a b h; exact Nat.add_right_cancel h)
  · intro n
    dsimp [realBinaryTerm]
    split <;> simp [norm_pow]

noncomputable def realBinaryReadout (w : (ℕ → Bool)) : ℝ :=
  ∑' n : ℕ, realBinaryTerm w n

theorem realBinaryReadout_nonnegative (w : (ℕ → Bool)) :
    0 ≤ realBinaryReadout w := by
  apply tsum_nonneg
  intro n
  dsimp [realBinaryTerm]
  positivity

theorem realBinaryReadout_eq_zero_iff (w : ℕ → Bool) :
    realBinaryReadout w = 0 ↔ ∀ n, w n = false := by
  constructor
  · intro h n
    cases hbit : w n with
    | false => rfl
    | true =>
        have hterm_pos : 0 < realBinaryTerm w n := by
          simp [realBinaryTerm, hbit]
        have hterm_le : realBinaryTerm w n ≤ realBinaryReadout w := by
          exact (realBinaryTerm_summable w).le_tsum n (fun m _ => by
            dsimp [realBinaryTerm]
            positivity)
        have hterm_zero : realBinaryTerm w n = 0 := by
          apply le_antisymm
          · simpa [h] using hterm_le
          · dsimp [realBinaryTerm]
            positivity
        linarith
  · intro h
    have hzero : realBinaryTerm w = 0 := by
      funext n
      dsimp [realBinaryTerm]
      rw [h n]
      simp
    change (∑' n : ℕ, realBinaryTerm w n) = 0
    rw [hzero]
    simp

theorem realBinaryReadout_le_one (w : (ℕ → Bool)) :
    realBinaryReadout w ≤ 1 := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_norm_lt_one (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa [Function.comp_def] using
      hgeom.comp_injective (i := fun n : ℕ => n + 1)
        (by intro a b h; exact Nat.add_right_cancel h)
  have hsum : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
    have hterm : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) =
        (fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) := by
      funext n
      rw [pow_add]
      ring
    letI : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
    rw [hterm, tsum_mul_left]
    have hseries : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
      convert (tsum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)) using 1 <;>
        norm_num
    rw [hseries]
    norm_num
  dsimp [realBinaryReadout]
  calc
    (∑' n : ℕ, realBinaryTerm w n) ≤
        ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) := by
      exact (realBinaryTerm_summable w).tsum_le_tsum
        (fun n => by
          dsimp [realBinaryTerm]
          split <;> simp)
        hshift
    _ = 1 := hsum

theorem realBinaryReadout_mem_unitInterval (w : (ℕ → Bool)) :
    realBinaryReadout w ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨realBinaryReadout_nonnegative w, realBinaryReadout_le_one w⟩

theorem realBinaryReadout_complement (w : (ℕ → Bool)) :
    realBinaryReadout (fun n => !w n) + realBinaryReadout w = 1 := by
  have hcomp : Summable (realBinaryTerm (fun n => !w n)) :=
    realBinaryTerm_summable (fun n => !w n)
  have hw : Summable (realBinaryTerm w) := realBinaryTerm_summable w
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_norm_lt_one (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa [Function.comp_def] using
      hgeom.comp_injective (i := fun n : ℕ => n + 1)
        (by intro a b h; exact Nat.add_right_cancel h)
  have hsum : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
    have hterm : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) =
        (fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) := by
      funext n
      rw [pow_add]
      ring
    letI : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
    rw [hterm, tsum_mul_left]
    have hseries : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
      convert (tsum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)) using 1 <;>
        norm_num
    rw [hseries]
    norm_num
  letI : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
  calc
    realBinaryReadout (fun n => !w n) + realBinaryReadout w =
        ∑' n : ℕ, (realBinaryTerm (fun n => !w n) n + realBinaryTerm w n) := by
          change
            (∑' n : ℕ, realBinaryTerm (fun n => !w n) n) +
                ∑' n : ℕ, realBinaryTerm w n = _
          exact (hcomp.tsum_add hw).symm
    _ = ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) := by
      apply tsum_congr
      intro n
      dsimp [realBinaryTerm]
      cases h : w n <;> simp [h]
    _ = 1 := hsum

theorem realBinaryReadout_eq_one_iff (w : ℕ → Bool) :
    realBinaryReadout w = 1 ↔ ∀ n, w n = true := by
  constructor
  · intro h n
    have hzero : realBinaryReadout (fun k => !w k) = 0 := by
      linarith [realBinaryReadout_complement w]
    have hfalse : ∀ k, (!w k) = false :=
      (realBinaryReadout_eq_zero_iff (fun k => !w k)).mp hzero
    cases hbit : w n with
    | false =>
        have := hfalse n
        simp [hbit] at this
    | true => rfl
  · intro h
    have hzero : realBinaryReadout (fun k => !w k) = 0 := by
      apply (realBinaryReadout_eq_zero_iff (fun k => !w k)).mpr
      intro n
      simp [h n]
    linarith [realBinaryReadout_complement w]

theorem realBinaryReadout_complement_eq_one_sub
    (w : (ℕ → Bool)) :
    realBinaryReadout (fun n => !w n) = 1 - realBinaryReadout w := by
  linarith [realBinaryReadout_complement w]

end InfoGeometry.Canonical.CantorBoundaryReadoutBounds
