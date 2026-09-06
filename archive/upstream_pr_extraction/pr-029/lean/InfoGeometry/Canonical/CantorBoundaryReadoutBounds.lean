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

def realBinaryTerm (w : InfiniteBinaryWordSpace) (n : ℕ) : ℝ :=
  (if w n then 1 else 0) * (1 / 2 : ℝ) ^ (n + 1)

theorem realBinaryTerm_summable (w : InfiniteBinaryWordSpace) :
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

noncomputable def realBinaryReadout (w : InfiniteBinaryWordSpace) : ℝ :=
  ∑' n : ℕ, realBinaryTerm w n

theorem realBinaryReadout_nonnegative (w : InfiniteBinaryWordSpace) :
    0 ≤ realBinaryReadout w := by
  apply tsum_nonneg
  intro n
  dsimp [realBinaryTerm]
  positivity

theorem realBinaryReadout_le_one (w : InfiniteBinaryWordSpace) :
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

theorem realBinaryReadout_mem_unitInterval (w : InfiniteBinaryWordSpace) :
    realBinaryReadout w ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨realBinaryReadout_nonnegative w, realBinaryReadout_le_one w⟩

end InfoGeometry.Canonical.CantorBoundaryReadoutBounds
