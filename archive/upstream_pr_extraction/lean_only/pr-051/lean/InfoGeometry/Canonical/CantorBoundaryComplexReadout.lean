import Mathlib.Tactic
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBoundaryReadoutBounds

/-!
# Complex readout of the binary Cantor boundary

This owner separates the genuine binary carrier from the earlier exploratory
`ℕ → ℂ` readout.  It proves only summability of the binary geometric series;
the intertwining identity is deliberately left for the next theorem layer.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryComplexReadout

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

def binaryDigit (b : Bool) : ℂ :=
  if b then 1 else 0

def binaryTerm (w : (ℕ → Bool)) (n : ℕ) : ℂ :=
  binaryDigit (w n) * (1 / 2 : ℂ) ^ (n + 1)

theorem binaryDigit_eq_ofReal (b : Bool) :
    binaryDigit b = Complex.ofReal (if b then (1 : ℝ) else 0) := by
  cases b <;> rfl

theorem binaryTerm_eq_ofReal_realTerm
    (w : (ℕ → Bool)) (n : ℕ) :
    binaryTerm w n = Complex.ofReal (realBinaryTerm w n) := by
  cases h : w n <;>
    simp [binaryTerm, binaryDigit, realBinaryTerm, h, Complex.ofReal_pow]

theorem binaryTerm_summable (w : (ℕ → Bool)) :
    Summable (binaryTerm w) := by
  apply Summable.of_norm_bounded (f := binaryTerm w)
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  · have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
      exact summable_geometric_of_norm_lt_one (by norm_num)
    simpa [Function.comp_def] using
      hgeom.comp_injective (i := fun n : ℕ => n + 1)
        (by intro a b h; exact Nat.add_right_cancel h)
  · intro n
    dsimp [binaryTerm, binaryDigit]
    split <;> simp [norm_pow]

noncomputable def binaryReadout (w : (ℕ → Bool)) : ℂ :=
  ∑' n : ℕ, binaryTerm w n

theorem binaryReadout_eq_ofReal (w : (ℕ → Bool)) :
    binaryReadout w = Complex.ofReal (realBinaryReadout w) := by
  rw [binaryReadout, realBinaryReadout, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact binaryTerm_eq_ofReal_realTerm w n

theorem binaryReadout_im (w : (ℕ → Bool)) :
    (binaryReadout w).im = 0 := by
  rw [binaryReadout_eq_ofReal]
  rfl

theorem binaryReadout_eq_zero_iff (w : ℕ → Bool) :
    binaryReadout w = 0 ↔ ∀ n, w n = false := by
  rw [binaryReadout_eq_ofReal]
  simpa using realBinaryReadout_eq_zero_iff w

theorem binaryReadout_eq_one_iff (w : ℕ → Bool) :
    binaryReadout w = 1 ↔ ∀ n, w n = true := by
  rw [binaryReadout_eq_ofReal]
  simpa using realBinaryReadout_eq_one_iff w

theorem binaryReadout_norm_le_one (w : (ℕ → Bool)) :
    ‖binaryReadout w‖ ≤ 1 := by
  rw [binaryReadout_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realBinaryReadout_nonnegative w)]
  exact realBinaryReadout_le_one w

theorem binaryDigit_complement_add (b : Bool) :
    binaryDigit (!b) + binaryDigit b = 1 := by
  cases b <;> simp [binaryDigit]

theorem binary_readout_complement (w : (ℕ → Bool)) :
    binaryReadout (fun n => !w n) + binaryReadout w = 1 := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℂ) ^ n) := by
    exact summable_geometric_of_norm_lt_one (by norm_num)
  have hsum : (∑' n : ℕ, (1 / 2 : ℂ) ^ n) = 2 := by
    convert (tsum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℂ)) (by norm_num)) using 1 <;>
      norm_num
  have hbase : (∑' n : ℕ, (1 / 2 : ℂ) ^ (n + 1)) = 1 := by
    have hterm : (fun n : ℕ => (1 / 2 : ℂ) ^ (n + 1)) =
        (fun n => (1 / 2 : ℂ) * (1 / 2 : ℂ) ^ n) := by
      funext n
      rw [pow_add]
      ring
    rw [hterm, hgeom.tsum_mul_left, hsum]
    norm_num
  rw [show (1 : ℂ) = ∑' n : ℕ, (1 / 2 : ℂ) ^ (n + 1) by exact hbase.symm]
  dsimp [binaryReadout]
  rw [← Summable.tsum_add (binaryTerm_summable (fun n => !w n)) (binaryTerm_summable w)]
  apply tsum_congr
  intro n
  dsimp [binaryTerm]
  rw [← add_mul]
  rw [binaryDigit_complement_add]
  ring

theorem binary_readout_complement_eq_one_sub
    (w : (ℕ → Bool)) :
    binaryReadout (fun n => !w n) = 1 - binaryReadout w := by
  exact (eq_sub_iff_add_eq).2 (binary_readout_complement w)

theorem binary_readout_intertwining_of_pointwise_complement
    (tomita : (ℕ → Bool) → (ℕ → Bool))
    (w : (ℕ → Bool))
    (h_tomita : ∀ n, tomita w n = !w n) :
    binaryReadout (tomita w) + binaryReadout w = 1 := by
  have h_word : tomita w = fun n => !w n := by
    funext n
    exact h_tomita n
  rw [h_word]
  exact binary_readout_complement w

theorem binary_readout_fixed_state_on_critical_line
    (tomita : (ℕ → Bool) → (ℕ → Bool))
    (w : (ℕ → Bool))
    (h_tomita : ∀ n, tomita w n = !w n)
    (h_invariant : binaryReadout (tomita w) = star (binaryReadout w)) :
    (binaryReadout w).re = 1 / 2 := by
  have h_complement := binary_readout_intertwining_of_pointwise_complement
    tomita w h_tomita
  have h_fixed : 1 - star (binaryReadout w) = binaryReadout w := by
    rw [← h_invariant]
    calc
      1 - binaryReadout (tomita w) =
          (binaryReadout (tomita w) + binaryReadout w) -
            binaryReadout (tomita w) := by rw [h_complement]
      _ = binaryReadout w := by ring
  have h_re := congrArg Complex.re h_fixed
  change 1 - (binaryReadout w).re = (binaryReadout w).re at h_re
  linarith

end InfoGeometry.Canonical.CantorBoundaryComplexReadout
