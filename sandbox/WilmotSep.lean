import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

namespace ScratchWilmot

open Matrix
open InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

noncomputable def bryantGen (m : Fin 14) : Matrix (Fin 7) (Fin 7) ℝ :=
  match m with
  | 0  => (1/2 : ℝ) • (skewGen 1 2 - skewGen 3 4)
  | 1  => (1/2 : ℝ) • (- skewGen 0 2 - skewGen 3 5)
  | 2  => (1/2 : ℝ) • (skewGen 0 1 + skewGen 3 6)
  | 3  => (1/2 : ℝ) • (skewGen 0 4 + skewGen 1 5)
  | 4  => (1/2 : ℝ) • (skewGen 0 3 - skewGen 1 6)
  | 5  => (1/2 : ℝ) • (skewGen 0 6 + skewGen 1 3)
  | 6  => (1/2 : ℝ) • (- skewGen 0 5 - skewGen 1 4)
  | 7  => (1/2 : ℝ) • (skewGen 3 4 - skewGen 5 6)
  | 8  => (1/2 : ℝ) • (skewGen 3 5 + skewGen 4 6)
  | 9  => (1/2 : ℝ) • (- skewGen 3 6 + skewGen 4 5)
  | 10 => (1/2 : ℝ) • (- skewGen 1 5 - skewGen 2 6)
  | 11 => (1/2 : ℝ) • (- skewGen 1 6 + skewGen 2 5)
  | 12 => (1/2 : ℝ) • (- skewGen 0 6 + skewGen 2 4)
  | 13 => (1/2 : ℝ) • (skewGen 1 4 - skewGen 2 3)

/-- Separating row coordinate: each generator's unique nonzero slot. -/
def sr : Fin 14 → Fin 7 :=
  fun i => match i with
  | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0
  | 7 => 5 | 8 => 6 | 9 => 5 | 10 => 2 | 11 => 2 | 12 => 2 | 13 => 1

/-- Separating column coordinate. -/
def ss : Fin 14 → Fin 7 :=
  fun i => match i with
  | 0 => 2 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
  | 7 => 6 | 8 => 6 | 9 => 5 | 10 => 6 | 11 => 5 | 12 => 4 | 13 => 4

set_option maxHeartbeats 2000000 in
theorem bryantGen_diag_ne_zero (i : Fin 14) :
    bryantGen i (sr i) (ss i) ≠ 0 := by
  fin_cases i <;> simp [bryantGen, sr, ss, skewGen] <;> norm_num

end ScratchWilmot
