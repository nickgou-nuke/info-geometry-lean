import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite diagonal-gauge invariants

For a matrix `F`, a positive row/column rescaling has the form
`F' i j = r i * F i j * c j`.  This file records only the finite algebraic
invariants of that action.  It does not assert existence or convergence of a
Sinkhorn iteration.

The multiplicative three-cycle ratio is the exponential form of a cycle
affinity.  The cross-ratio is the corresponding four-entry invariant.
-/

namespace InfoGeometry.Inference.FiniteDiagonalGaugeInvariants

variable {ι : Type*}

def diagonalGauge (r c : ι → ℝ) (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => r i * F i j * c j

def cycleRatio (F : Matrix ι ι ℝ) (i j k : ι) : ℝ :=
  (F i j * F j k * F k i) / (F j i * F k j * F i k)

def crossRatio (F : Matrix ι ι ℝ) (i k j l : ι) : ℝ :=
  (F i j * F k l) / (F i l * F k j)

theorem cycleRatio_diagonalGauge_invariant
    (r c : ι → ℝ) (F : Matrix ι ι ℝ) (i j k : ι)
    (hr_i : r i ≠ 0) (hr_j : r j ≠ 0) (hr_k : r k ≠ 0)
    (hc_i : c i ≠ 0) (hc_j : c j ≠ 0) (hc_k : c k ≠ 0)
    (hji : F j i ≠ 0) (hkj : F k j ≠ 0) (hik : F i k ≠ 0) :
    cycleRatio (diagonalGauge r c F) i j k = cycleRatio F i j k := by
  unfold cycleRatio diagonalGauge
  field_simp [hji, hkj, hik, hr_i, hr_j, hr_k, hc_i, hc_j, hc_k]
  ring

theorem crossRatio_diagonalGauge_invariant
    (r c : ι → ℝ) (F : Matrix ι ι ℝ) (i k j l : ι)
    (hr_i : r i ≠ 0) (hr_k : r k ≠ 0)
    (hc_j : c j ≠ 0) (hc_l : c l ≠ 0)
    (hil : F i l ≠ 0) (hkj : F k j ≠ 0) :
    crossRatio (diagonalGauge r c F) i k j l = crossRatio F i k j l := by
  unfold crossRatio diagonalGauge
  field_simp [hil, hkj, hr_i, hr_k, hc_j, hc_l]
  ring

end InfoGeometry.Inference.FiniteDiagonalGaugeInvariants
